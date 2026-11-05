/* SPDX-License-Identifier: GPL-3.0-or-later
 * Ghost-Control - Only for 小鸡启明星二代 VID=0x0e6f PID=0x0184
 * USB HID → virtual DualSense devices on PS5
 * Hotplug: plug in any time, disconnect, wait replug, payload not exit
 */

#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
#include <pthread.h>
#include <fcntl.h>
#include <signal.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <dirent.h>
#include <netinet/in.h>
#include <arpa/inet.h>

#include <dev/usb/usb.h>
#include <dev/usb/usb_ioctl.h>
#include <dev/usb/usb_endian.h>

#ifdef __PROSPERO__
#include <ps5/kernel.h>
#include <ps5/klog.h>
#include <ps5/mdbg.h>
#endif

#include "shellui_pad.h"
#include "gc_types.h"
#include "usb_helpers.h"
#include "controller_ds4.h"

/* ── Logging ──────────────────────────────────────────────────────────── */
#define LOG_DIR  "/data/ghostpad"
#define LOG_PATH "/data/ghostpad/gc_status.log"
#define PID_PATH "/data/ghostpad/gc_main.pid"
#define LOG_MAX  480

static pthread_mutex_t g_log_lock = PTHREAD_MUTEX_INITIALIZER;
static int g_log_fd = -1;

void ghostpad_status_log_reset(void) {
    pthread_mutex_lock(&g_log_lock);
    if (g_log_fd >= 0) { close(g_log_fd); g_log_fd = -1; }
    mkdir(LOG_DIR, 0755);
    g_log_fd = open(LOG_PATH, O_WRONLY|O_CREAT|O_TRUNC, 0600);
    pthread_mutex_unlock(&g_log_lock);
}

void ghostpad_status_log(const char *fmt, ...) {
    char buf[LOG_MAX]; va_list ap;
    va_start(ap, fmt); vsnprintf(buf, sizeof(buf)-1, fmt, ap); va_end(ap);
    buf[LOG_MAX-1] = '\0';
    klog_printf("%s", buf);
    pthread_mutex_lock(&g_log_lock);
    if (g_log_fd >= 0) {
        size_t n = strnlen(buf, sizeof(buf));
        write(g_log_fd, buf, n);
        if (n && buf[n-1] != '\n') write(g_log_fd, "\n", 1);
    }
    pthread_mutex_unlock(&g_log_lock);
}
#define gp_log(...) ghostpad_status_log("[GC] " __VA_ARGS__)

/* ── SCE stubs ────────────────────────────────────────────────────────── */
extern int32_t sceUserServiceInitialize(void *params);
extern int32_t sceUserServiceGetInitialUser(int32_t *outUserId);
extern int32_t sceUserServiceGetForegroundUser(int32_t *outUserId);
extern int32_t scePadInit(void);
extern int32_t scePadSetProcessPrivilege(int32_t privilege);
extern int32_t scePadGetHandle(int32_t userId, int32_t type, int32_t index);
extern int32_t scePadVirtualDeviceAddDevice(void *param, int32_t deviceType);
extern int32_t scePadVirtualDeviceDeleteDevice(int32_t handle);
extern int32_t scePadVirtualDeviceInsertData(int32_t handle, const void *padData);
extern int32_t sceKernelSendNotificationRequest(int unk0, void *req, size_t size, int unk1);

#define VIRTUAL_DEVICE_TYPE_DUALSENSE 3

/* ── Multi-controller slots ───────────────────────────────────────────── */
#define MAX_SLOTS 4

typedef struct {
    volatile int32_t handle;        /* VDA handle, -1 = slot free */
    volatile int     vdi_ready;
    volatile int     usb_active;    /* USB reader thread is running */
    volatile int     release_requested;
    volatile int     release_wait_neutral;
    volatile int     confirmed;     /* user pressed a button — assignment done */
    volatile int     usb_fd;        /* open ugen fd, -1 if none — for clean teardown */
    char             dev_path[32];  /* ugen path claimed by this slot */
    uint16_t         vid, pid;
    volatile uint64_t virtual_dev_id;
    volatile uint32_t inject_count;
} ctrl_slot_t;

static ctrl_slot_t     g_slots[MAX_SLOTS];
static pthread_mutex_t g_slot_lock = PTHREAD_MUTEX_INITIALIZER;
static int32_t         g_inject_uid = 0x10000000;
static volatile uint64_t g_last_physical_pad_dev = 0;
static uint64_t          g_virtual_id_history[32];
static unsigned          g_virtual_id_history_w = 0;

static volatile int    g_assign_slot = -1;

/* ── klog device-ID queue ─────────────────────────────────────────────── */
#define KLOG_QSIZE 16
static uint64_t        g_klog_q[KLOG_QSIZE];
static int             g_klog_qw = 0, g_klog_qr = 0;
static pthread_mutex_t g_klog_lock = PTHREAD_MUTEX_INITIALIZER;

typedef struct {
    uint64_t dev_id;
    int32_t  handle;
    int32_t  open_type;
} klog_open_pad_t;

#define KLOG_OPEN_PAD_COUNT 16
static klog_open_pad_t g_klog_open_pad[KLOG_OPEN_PAD_COUNT];
static unsigned        g_klog_open_pad_w = 0;

static void klog_open_pad_store(uint64_t dev_id, int32_t open_type, int32_t handle);
static int32_t klog_find_open_pad_handle(uint64_t dev_id);
static int32_t klog_wait_open_pad_handle(uint64_t dev_id, int ms);
static int is_our_virtual_device_id(uint64_t dev_id);
static void remember_virtual_device_id(uint64_t dev_id);

static void klog_enqueue(uint64_t id) {
    pthread_mutex_lock(&g_klog_lock);
    int next = (g_klog_qw + 1) % KLOG_QSIZE;
    if (next != g_klog_qr) { g_klog_q[g_klog_qw] = id; g_klog_qw = next; }
    pthread_mutex_unlock(&g_klog_lock);
}

static uint64_t klog_dequeue_ms(int ms) {
    for (int t = 0; t < ms; t += 100) {
        pthread_mutex_lock(&g_klog_lock);
        if (g_klog_qw != g_klog_qr) {
            uint64_t id = g_klog_q[g_klog_qr];
            g_klog_qr = (g_klog_qr + 1) % KLOG_QSIZE;
            pthread_mutex_unlock(&g_klog_lock);
            return id;
        }
        pthread_mutex_unlock(&g_klog_lock);
        usleep(100000);
    }
    return 0;
}

/* ── Notification ─────────────────────────────────────────────────────── */
typedef struct { char _unk[45]; char message[3075]; } NotifyRequest;
static void notify(const char *fmt, ...) {
    NotifyRequest req; va_list ap;
    memset(&req, 0, sizeof(req));
    va_start(ap, fmt); vsnprintf(req.message, sizeof(req.message), fmt, ap); va_end(ap);
    sceKernelSendNotificationRequest(0, &req, sizeof(req), 0);
}

/* ── klog capture thread ──────────────────────────────────────────────── */
static uint64_t parse_hex_str(const char *s) {
    uint64_t v = 0;
    while (*s) {
        char c = *s++;
        if      (c >= '0' && c <= '9') v = (v<<4)|(c-'0');
        else if (c >= 'a' && c <= 'f') v = (v<<4)|(c-'a'+10);
        else if (c >= 'A' && c <= 'F') v = (v<<4)|(c-'A'+10);
        else break;
    }
    return v;
}

static uint64_t parse_uint_auto(const char *s, const char **endp, int *ok) {
    uint64_t v = 0;
    int base = 10;
    int got = 0;

    while (*s == ' ' || *s == '\t')
        s++;
    if (s[0] == '0' && (s[1] == 'x' || s[1] == 'X')) {
        base = 16;
        s += 2;
    }

    while (*s) {
        char c = *s;
        int d;
        if (c >= '0' && c <= '9') d = c - '0';
        else if (c >= 'a' && c <= 'f') d = c - 'a' + 10;
        else if (c >= 'A' && c <= 'F') d = c - 'A' + 10;
        else break;
        if (d >= base) break;
        v = (v * (uint64_t)base) + (uint64_t)d;
        got = 1;
        s++;
    }

    if (endp) *endp = s;
    if (ok) *ok = got;
    return v;
}

static int parse_open_pad_line(const char *line, uint64_t *out_dev_id,
                               int32_t *out_open_type, int32_t *out_open_index,
                               int32_t *out_handle) {
    const char *open = strstr(line, "Open Pad [");
    if (!open)
        return 0;

    const char *p = open + 10;
    int ok_dev = 0;
    uint64_t dev_id = parse_uint_auto(p, &p, &ok_dev);
    if (!ok_dev)
        return 0;

    const char *comma = strchr(p, ',');
    if (!comma)
        return 0;
    comma++;

    int ok_type = 0;
    uint64_t open_type = parse_uint_auto(comma, &p, &ok_type);
    if (!ok_type || open_type > 0x7fffffffU)
        return 0;

    comma = strchr(p, ',');
    if (!comma)
        return 0;
    comma++;

    int ok_index = 0;
    uint64_t open_index = parse_uint_auto(comma, &p, &ok_index);
    if (!ok_index || open_index > 0x7fffffffU)
        return 0;

    const char *ret = strstr(p, "ret=");
    if (!ret)
        return 0;
    ret += 4;

    int ok_ret = 0;
    uint64_t h = parse_uint_auto(ret, NULL, &ok_ret);
    if (!ok_ret || h > 0x7fffffffu)
        return 0;

    *out_dev_id = dev_id;
    *out_open_type = (int32_t)open_type;
    *out_open_index = (int32_t)open_index;
    *out_handle = (int32_t)h;
    return 1;
}

static void parse_klog_line(const char *line) {
    if (strstr(line, "[payload.elf] [GC]") ||
        strstr(line, "[payload.elf] [Ghostpad]")) {
        return;
    }

    uint64_t open_dev_id = 0;
    int32_t open_type = -1;
    int32_t open_index = -1;
    int32_t open_handle = -1;
    if (!strstr(line, "[GC] klog: Open Pad") &&
        parse_open_pad_line(line, &open_dev_id, &open_type, &open_index, &open_handle)) {
        klog_open_pad_store(open_dev_id, open_type, open_handle);
    }

    if (strstr(line, "[GC] klog:"))           return;
    if (!strstr(line, "DEVICE_ADDED"))        return;
    if (!strstr(line, "subType:22"))          return;
    const char *p = strstr(line, "DeviceId:0x");
    if (!p) p = strstr(line, "deviceId=0x");
    if (!p) return;
    p += 11;
    uint64_t id = parse_hex_str(p);
    if (!id) return;
    if (strstr(line, "capabilityBattery:0")) {
        gp_log("klog: VDA device 0x%llx\n", (unsigned long long)id);
        remember_virtual_device_id(id);
        klog_enqueue(id);
    }
}

static void *klog_capture_thread(void *arg) {
    (void)arg;
    char buf[512], line[1024]; size_t line_len = 0;
    int fd = open("/dev/klog", O_RDONLY);
    if (fd < 0) {
        gp_log("klog: /dev/klog errno=%d, trying TCP 127.0.0.1:3232\n", errno);
        struct sockaddr_in sin; int sock = socket(AF_INET, SOCK_STREAM, 0);
        if (sock < 0) return NULL;
        memset(&sin,0,sizeof(sin)); sin.sin_family=AF_INET;
        sin.sin_addr.s_addr=inet_addr("127.0.0.1"); sin.sin_port=htons(3232);
        for (int r=0; r<10; r++) {
            if (connect(sock,(struct sockaddr*)&sin,sizeof(sin))==0){fd=sock;gp_log("klog: connected\n");break;}
            usleep(500000);
        }
        if (fd<0){close(sock);return NULL;}
    }
    while (1) {
        ssize_t len = read(fd, buf, sizeof(buf));
        if (len < 0) { if (errno==EINTR) continue; break; }
        if (len == 0) { usleep(10000); continue; }
        for (ssize_t i=0; i<len; i++) {
            char c = buf[i];
            if (c=='\n'||line_len>=sizeof(line)-1){line[line_len]='\0';parse_klog_line(line);line_len=0;}
            else if (c!='\r') line[line_len++]=c;
        }
    }
    close(fd); return NULL;
}

/* ── VDI injection ────────────────────────────────────────────────────── */
static void inject_pad(int slot, const ScePadData *pad) {
    int32_t h = g_slots[slot].handle;
    if (h < 0 || !g_slots[slot].vdi_ready) return;
    int vr = scePadVirtualDeviceInsertData(h, pad);
    uint32_t n = ++g_slots[slot].inject_count;
    if ((n % 600) == 0)
        gp_log("slot[%d] VDI #%u ret=0x%08x\n", slot, n, (uint32_t)vr);
    static int vdi_err_logged = 0;
    if (vr != 0 && !vdi_err_logged) { gp_log("VDI error 0x%08x\n",(uint32_t)vr); vdi_err_logged=1; }
}

/* ── ugen detection ───────────────────────────────────────────────────── */
#define VID_CHICKEN  0x0e6fu
#define PID_CHICKEN  0x0184u

static int match_known_vidpid(uint16_t vid, uint16_t pid,
                              uint16_t *out_vid, uint16_t *out_pid) {
    if (vid == VID_CHICKEN && pid == PID_CHICKEN) {
        *out_vid = vid; *out_pid = pid;
        return 1;
    }
    return 0;
}

static int is_our_virtual_device_id(uint64_t dev_id) {
    if (!dev_id)
        return 0;
    for (int s = 0; s < MAX_SLOTS; s++) {
        if (g_slots[s].virtual_dev_id == dev_id)
            return 1;
    }
    for (int i = 0; i < (int)(sizeof(g_virtual_id_history) / sizeof(g_virtual_id_history[0])); i++) {
        if (g_virtual_id_history[i] == dev_id)
            return 1;
    }
    return 0;
}

static void remember_virtual_device_id(uint64_t dev_id) {
    if (!dev_id)
        return;

    pthread_mutex_lock(&g_slot_lock);
    for (int i = 0; i < (int)(sizeof(g_virtual_id_history) / sizeof(g_virtual_id_history[0])); i++) {
        if (g_virtual_id_history[i] == dev_id) {
            pthread_mutex_unlock(&g_slot_lock);
            return;
        }
    }
    g_virtual_id_history[g_virtual_id_history_w %
                         (sizeof(g_virtual_id_history) / sizeof(g_virtual_id_history[0]))] = dev_id;
    g_virtual_id_history_w++;
    pthread_mutex_unlock(&g_slot_lock);
}

static void klog_open_pad_store(uint64_t dev_id, int32_t open_type, int32_t handle) {
    if (!dev_id || handle < 0)
        return;
    pthread_mutex_lock(&g_klog_lock);
    g_klog_open_pad[g_klog_open_pad_w % KLOG_OPEN_PAD_COUNT].dev_id = dev_id;
    g_klog_open_pad[g_klog_open_pad_w % KLOG_OPEN_PAD_COUNT].handle = handle;
    g_klog_open_pad[g_klog_open_pad_w % KLOG_OPEN_PAD_COUNT].open_type = open_type;
    g_klog_open_pad_w++;
    pthread_mutex_unlock(&g_klog_lock);
}

static int32_t klog_find_open_pad_handle(uint64_t dev_id) {
    int32_t handle = -1;
    pthread_mutex_lock(&g_klog_lock);
    for (int i = 0; i < KLOG_OPEN_PAD_COUNT; i++) {
        if (g_klog_open_pad[i].dev_id == dev_id) {
            handle = g_klog_open_pad[i].handle;
            break;
        }
    }
    pthread_mutex_unlock(&g_klog_lock);
    return handle;
}

static int32_t klog_wait_open_pad_handle(uint64_t dev_id, int ms) {
    for (int t = 0; t <= ms; t += 100) {
        int32_t handle = klog_find_open_pad_handle(dev_id);
        if (handle >= 0)
            return handle;
        usleep(100000);
    }
    return -1;
}

/* Probe a /dev/ugen* path */
static int probe_one_path(const char *path, uint16_t *out_vid, uint16_t *out_pid) {
    int fd = open(path, O_RDWR|O_NONBLOCK);
    if (fd < 0) return 0;

    struct usb_device_descriptor desc;
    memset(&desc, 0, sizeof(desc));
    if (ioctl(fd, USB_GET_DEVICE_DESC, &desc) == 0) {
        uint16_t vid = UGETW(desc.idVendor);
        uint16_t pid = UGETW(desc.idProduct);
        gp_log("scan: %s VID=0x%04x PID=0x%04x\n", path, vid, pid);
        if (match_known_vidpid(vid, pid, out_vid, out_pid)) {
            close(fd);
            return 1;
        }
    } else {
        gp_log("scan: %s USB_GET_DEVICE_DESC errno=%d\n", path, errno);
    }
    close(fd);
    return 0;
}

/* ── Create VDA and force_bind for a slot ─────────────────────────────── */
static int32_t create_vda_for_slot(int slot) {
    struct { int32_t size; int32_t userId; int32_t pad[6]; } vdp;
    const int32_t SEN = (int32_t)0xDEADBEEFu;

    memset(&vdp,0,sizeof(vdp)); vdp.size=sizeof(vdp); vdp.userId=1;
    for(int k=0;k<6;k++) vdp.pad[k]=SEN;

    gp_log("slot[%d] 小鸡启明星二代 VDA create\n", slot);
    int ret = scePadVirtualDeviceAddDevice(&vdp, VIRTUAL_DEVICE_TYPE_DUALSENSE);
    gp_log("slot[%d] VDA ret=0x%08x\n", slot, (uint32_t)ret);

    int32_t handle = (ret > 0) ? ret : -1;
    for(int k=0;k<6;k++){
        if(vdp.pad[k]!=SEN && vdp.pad[k]>0){if(handle<0)handle=vdp.pad[k];break;}
    }

    uint64_t dev_id = klog_dequeue_ms(10000);
    if (dev_id) {
        g_slots[slot].virtual_dev_id = dev_id;
        remember_virtual_device_id(dev_id);
        int br = shellui_pad_force_bind(dev_id, g_inject_uid);
        gp_log("slot[%d] force_bind(0x%llx, 0x%08x) ret=%d\n",
               slot, (unsigned long long)dev_id, (uint32_t)g_inject_uid, br);

        int32_t open_handle = klog_wait_open_pad_handle(dev_id, 4000);
        if (open_handle >= 0) {
            gp_log("slot[%d] klog Open Pad remote handle=0x%x for dev=0x%llx\n",
                   slot, (uint32_t)open_handle, (unsigned long long)dev_id);
        } else {
            gp_log("slot[%d] no Open Pad remote handle for dev=0x%llx\n",
                   slot, (unsigned long long)dev_id);
        }
        handle = (int32_t)(dev_id & 0xffffffffu);
        gp_log("slot[%d] using local VDA handle=0x%x for VDI\n",
               slot, (uint32_t)handle);
    } else if (handle >= 0) {
        gp_log("slot[%d] klog timeout — using direct handle %d\n", slot, handle);
    } else {
        gp_log("slot[%d] GetHandle scan...\n", slot);
        static const int32_t uids[]={1,0x10000000,(int32_t)0xffffffff};
        for(int ui=0;ui<3&&handle<0;ui++)
            for(int idx=0;idx<8&&handle<0;idx++){
                handle=scePadGetHandle(uids[ui],3,idx);
                if(handle>=0) gp_log("slot[%d] GetHandle uid=0x%08x idx=%d h=%d\n",
                                     slot,(uint32_t)uids[ui],idx,handle);
            }
    }
    if (handle>=0)
        gp_log("slot[%d] VDI handle=0x%x ready\n", slot, (uint32_t)handle);
    else
        gp_log("slot[%d] ERROR: no VDA handle\n", slot);
    return handle;
}

/* ── USB HID thread ───────────────────────────────────────────────────── */
typedef struct {
    int      slot;
    char     dev_path[32];
    uint16_t vid, pid;
} usb_thread_arg_t;

static void *usb_hid_thread(void *arg) {
    usb_thread_arg_t *targ = (usb_thread_arg_t *)arg;
    int slot = targ->slot;
    char dev_path[32]; memcpy(dev_path, targ->dev_path, sizeof(dev_path));
    uint16_t vid = targ->vid, pid = targ->pid;
    free(targ);

    struct usb_fs_endpoint eps[2];
    struct usb_fs_init     init;
    struct usb_fs_open     fs_open;
    struct usb_fs_start    start;
    struct usb_fs_complete complete;
    struct usb_fs_stop     stop;
    struct usb_fs_close    fs_close;
    struct usb_fs_uninit   uninit;
    uint8_t  buf[64];
    void    *buffers[1]; uint32_t lengths[1];
    int fd = -1, out_opened = 0;
    int usb_ready_notified = 0;

    gp_log("slot[%d] USB thread: %s VID=0x%04x PID=0x%04x\n",
           slot, dev_path, vid, pid);

    fd = open(dev_path, O_RDWR);
    if (fd < 0) { gp_log("slot[%d] open fail errno=%d\n", slot, errno); goto exit_slot; }

    { int ii; for(ii=0;ii<4;ii++){int i2=ii; ioctl(fd,USB_IFACE_DRIVER_DETACH,&i2);} }
    usleep(100000);

    memset(eps,0,sizeof(eps)); memset(&init,0,sizeof(init));
    init.pEndpoints=eps; init.ep_index_max=2;
    if (ioctl(fd,USB_FS_INIT,&init)!=0){
        gp_log("slot[%d] FS_INIT fail errno=%d\n",slot,errno);
        close(fd); goto exit_slot;
    }

    memset(&fs_open,0,sizeof(fs_open));
    fs_open.ep_index=0; fs_open.ep_no=DS4_EP_IN;
    fs_open.max_bufsize=64; fs_open.max_frames=1;
    int in_ok = (ioctl(fd,USB_FS_OPEN,&fs_open)==0);
    if (!in_ok) {
        memset(&fs_open,0,sizeof(fs_open));
        fs_open.ep_index=0; fs_open.ep_no=DS4_EP_IN_ALT;
        fs_open.max_bufsize=64; fs_open.max_frames=1;
        in_ok = (ioctl(fd,USB_FS_OPEN,&fs_open)==0);
        if (in_ok) gp_log("slot[%d] IN ep=0x81\n", slot);
    } else {
        gp_log("slot[%d] IN ep=0x84\n", slot);
    }
    if (!in_ok) {
        gp_log("slot[%d] IN fail errno=%d\n",slot,errno);
        goto uninit_exit;
    }
    gp_log("slot[%d] IN maxpkt=%u\n", slot, (unsigned)fs_open.max_packet_length);

    buffers[0]=buf; lengths[0]=64;
    eps[0].ppBuffer=buffers; eps[0].pLength=lengths; eps[0].nFrames=1;
    eps[0].timeout=50; eps[0].flags=USB_FS_FLAG_SINGLE_SHORT_OK|USB_FS_FLAG_MULTI_SHORT_OK;

    memset(&fs_open,0,sizeof(fs_open));
    fs_open.ep_index=1; fs_open.ep_no=DS4_EP_OUT;
    fs_open.max_bufsize=64; fs_open.max_frames=1;
    out_opened = (ioctl(fd,USB_FS_OPEN,&fs_open)==0) ? 1 : 0;
    if (!out_opened) {
        memset(&fs_open,0,sizeof(fs_open));
        fs_open.ep_index=1; fs_open.ep_no=DS4_EP_OUT_ALT;
        fs_open.max_bufsize=64; fs_open.max_frames=1;
        out_opened = (ioctl(fd,USB_FS_OPEN,&fs_open)==0) ? 1 : 0;
    }
    gp_log("slot[%d] OUT opened=%d\n", slot, out_opened);

main_loop:
    g_slots[slot].usb_fd = fd;
    while (1) {
        memset(buf,0,64);
        buffers[0]=buf; lengths[0]=64;
        eps[0].ppBuffer=buffers; eps[0].pLength=lengths;
        eps[0].aFrames=0; eps[0].status=0;

        memset(&start,0,sizeof(start)); start.ep_index=0;
        if (ioctl(fd,USB_FS_START,&start)!=0) {
            if (errno==EBUSY){
                memset(&stop,0,sizeof(stop)); stop.ep_index=0; ioctl(fd,USB_FS_STOP,&stop);
                usleep(5000);
            } else if (errno==ENXIO||errno==ENOTTY){
                gp_log("slot[%d] START errno=%d — device unplugged\n",slot,errno); goto reinit;
            } else {
                gp_log("slot[%d] START fatal errno=%d\n",slot,errno); goto reinit;
            }
            continue;
        }

        int ok=0, cerr=0, cw=0;
        for(cw=0;cw<60;cw++){
            memset(&complete,0,sizeof(complete)); complete.ep_index=0;
            if(ioctl(fd,USB_FS_COMPLETE,&complete)==0){ok=1;break;}
            cerr=errno;
            if(cerr==ENXIO||cerr==ENOTTY){gp_log("slot[%d] COMPLETE errno=%d — unplugged\n",slot,cerr);goto reinit;}
            if(cerr!=EBUSY) break;
            usleep(500);
        }
        if(!ok){
            memset(&stop,0,sizeof(stop)); stop.ep_index=0; ioctl(fd,USB_FS_STOP,&stop);
            continue;
        }
        if(lengths[0]<1) continue;

        uint32_t len = lengths[0];

        ScePadData pad; memset(&pad,0,sizeof(pad)); pad.quat.w=1.0f;
        int injected = ds4_handle_packet(fd, eps, buf, len, &pad);

        if (injected > 0) {
            if (!usb_ready_notified) {
                notify("Ghost-Control: slot[%d] 小鸡启明星二代 已激活", slot);
                usb_ready_notified = 1;
            }
            if (!g_slots[slot].confirmed && pad.buttons != 0) {
                g_slots[slot].confirmed = 1;
                if (g_assign_slot == slot) g_assign_slot = -1;
                gp_log("slot[%d] assignment confirmed (button press)\n", slot);
            }
            inject_pad(slot, &pad);
        }
    }

reinit:
    g_slots[slot].usb_fd = -1;
    if (usb_ready_notified) { notify("Ghost-Control: slot[%d] 手柄断开，等待重新插拔", slot); usb_ready_notified=0; }
    memset(&stop,0,sizeof(stop)); stop.ep_index=0; ioctl(fd,USB_FS_STOP,&stop);
    if (out_opened) {
        memset(&fs_close,0,sizeof(fs_close)); fs_close.ep_index=1; ioctl(fd,USB_FS_CLOSE,&fs_close);
        out_opened=0;
    }
    memset(&fs_close,0,sizeof(fs_close)); fs_close.ep_index=0; ioctl(fd,USB_FS_CLOSE,&fs_close);
uninit_exit:
    memset(&uninit,0,sizeof(uninit)); ioctl(fd,USB_FS_UNINIT,&uninit);
    close(fd); fd=-1;

exit_slot:
    gp_log("slot[%d] USB线程退出，释放槽位，管理器继续扫描等待重插\n", slot);
    uint64_t vdev = g_slots[slot].virtual_dev_id;
    if (vdev) {
        int vdr = shellui_pad_disconnect_device(vdev);
        gp_log("slot[%d] disconnect virtual dev=0x%llx ret=%d\n",
               slot, (unsigned long long)vdev, vdr);
    }
    scePadVirtualDeviceDeleteDevice(g_slots[slot].handle);
    pthread_mutex_lock(&g_slot_lock);
    g_slots[slot].handle    = -1;
    g_slots[slot].vdi_ready = 0;
    g_slots[slot].usb_active= 0;
    g_slots[slot].release_requested = 0;
    g_slots[slot].release_wait_neutral = 0;
    g_slots[slot].usb_fd    = -1;
    g_slots[slot].virtual_dev_id = 0;
    g_slots[slot].dev_path[0] = '\0';
    pthread_mutex_unlock(&g_slot_lock);
    return NULL;
}

/* ── Controller manager thread ────────────────────────────────────────── */
static void *controller_manager_thread(void *arg) {
    (void)arg;
    int scan = 0;
    gp_log("Manager thread started (只识别小鸡启明星二代 MAX_SLOTS=%d)\n", MAX_SLOTS);

    while (1) {
        char ugen_paths[32][32];
        int n_paths = 0;
        DIR *dp = opendir("/dev");
        if (dp) {
            struct dirent *ent;
            while (n_paths < 32 && (ent = readdir(dp)) != NULL) {
                if (strncmp(ent->d_name, "ugen", 4) != 0) continue;
                const char *dot = strchr(ent->d_name, '.');
                if (!dot || dot[1] == '\0') continue;
                if (strcmp(dot, ".1") == 0) continue;
                snprintf(ugen_paths[n_paths], sizeof(ugen_paths[0]),
                         "/dev/%s", ent->d_name);
                n_paths++;
            }
            closedir(dp);
        }
        if ((scan % 5) == 0) gp_log("manager: scan #%d — %d ugen paths\n", scan, n_paths);

        for (int i = 0; i < n_paths; i++) {
            const char *path = ugen_paths[i];
            if (g_assign_slot >= 0) break;

            int busy = 0;
            pthread_mutex_lock(&g_slot_lock);
            for (int s = 0; s < MAX_SLOTS; s++) {
                if (g_slots[s].usb_active && strcmp(g_slots[s].dev_path, path) == 0) {
                    busy = 1; break;
                }
            }
            pthread_mutex_unlock(&g_slot_lock);
            if (busy) continue;

            uint16_t vid=0, pid=0;
            if (!probe_one_path(path, &vid, &pid)) continue;

            int slot = -1;
            pthread_mutex_lock(&g_slot_lock);
            for (int s = 0; s < MAX_SLOTS; s++) {
                if (g_slots[s].handle < 0 && !g_slots[s].usb_active) { slot=s; break; }
            }
            pthread_mutex_unlock(&g_slot_lock);

            if (slot < 0) {
                if ((scan % 5) == 0) gp_log("manager: all %d slots full\n", MAX_SLOTS);
                continue;
            }

            gp_log("manager: 小鸡启明星二代 at %s → slot[%d]\n", path, slot);
            notify("Ghost-Control: 小鸡启明星二代检测到，按下按键分配用户");

            pthread_mutex_lock(&g_slot_lock);
            strncpy(g_slots[slot].dev_path, path, sizeof(g_slots[slot].dev_path)-1);
            g_slots[slot].usb_active = 1;
            g_slots[slot].release_requested = 0;
            g_slots[slot].release_wait_neutral = 0;
            g_slots[slot].confirmed  = 0;
            g_slots[slot].vid = vid;
            g_slots[slot].pid = pid;
            pthread_mutex_unlock(&g_slot_lock);
            g_assign_slot = slot;

            int32_t handle = create_vda_for_slot(slot);
            if (handle < 0) {
                gp_log("manager: slot[%d] VDA失败，释放\n", slot);
                pthread_mutex_lock(&g_slot_lock);
                g_slots[slot].usb_active = 0;
                g_slots[slot].dev_path[0] = '\0';
                g_slots[slot].handle = -1;
                g_slots[slot].virtual_dev_id = 0;
                pthread_mutex_unlock(&g_slot_lock);
                g_assign_slot = -1;
                continue;
            }

            pthread_mutex_lock(&g_slot_lock);
            g_slots[slot].handle      = handle;
            g_slots[slot].vdi_ready   = 1;
            g_slots[slot].inject_count = 0;
            pthread_mutex_unlock(&g_slot_lock);

            usb_thread_arg_t *targ = malloc(sizeof(*targ));
            if (!targ) {
                gp_log("manager: malloc fail for slot[%d]\n", slot);
                scePadVirtualDeviceDeleteDevice(handle);
                pthread_mutex_lock(&g_slot_lock);
                g_slots[slot].handle=-1; g_slots[slot].vdi_ready=0;
                g_slots[slot].usb_active=0; g_slots[slot].dev_path[0]='\0';
                g_slots[slot].virtual_dev_id=0;
                pthread_mutex_unlock(&g_slot_lock);
                g_assign_slot = -1;
                continue;
            }
            targ->slot = slot;
            strncpy(targ->dev_path, path, sizeof(targ->dev_path)-1);
            targ->vid=vid; targ->pid=pid;

            pthread_t tid;
            if (pthread_create(&tid, NULL, usb_hid_thread, targ) != 0) {
                gp_log("manager: pthread_create fail slot[%d]\n", slot);
                free(targ);
                scePadVirtualDeviceDeleteDevice(handle);
                pthread_mutex_lock(&g_slot_lock);
                g_slots[slot].handle=-1; g_slots[slot].vdi_ready=0;
                g_slots[slot].usb_active=0; g_slots[slot].dev_path[0]='\0';
                g_slots[slot].virtual_dev_id=0;
                pthread_mutex_unlock(&g_slot_lock);
                g_assign_slot = -1;
            } else {
                pthread_detach(tid);
                gp_log("manager: slot[%d] USB thread started handle=0x%x\n",
                       slot, (uint32_t)handle);
                notify("Ghost-Control: slot[%d] 准备就绪，按按键分配", slot);
            }
            break;
        }

        static int assign_wait = 0;
        if (g_assign_slot >= 0) {
            if (++assign_wait > 6) {
                gp_log("manager: assignment timeout slot[%d] — release gate\n", g_assign_slot);
                g_assign_slot = -1;
                assign_wait = 0;
            }
        } else {
            assign_wait = 0;
        }

        scan++;
        if ((scan % 5) == 0) {
            int active = 0;
            for (int s = 0; s < MAX_SLOTS; s++)
                if (g_slots[s].usb_active) active++;
            if (active == 0 && (scan % 10) == 0)
                gp_log("manager: scan #%d — 等待小鸡手柄插入\n", scan);
        }
        usleep(2000000);
    }
    return NULL;
}

/* ── Credential elevation ─────────────────────────────────────────────── */
static void elevate_credentials(void) {
    pid_t p = getpid();
    uint8_t caps[16]; memset(caps,0xff,sizeof(caps));
    kernel_set_ucred_authid(p, 0x3800000000010003l);
    kernel_set_ucred_caps(p, caps);
}

/* ── main ─────────────────────────────────────────────────────────────── */
static void cleanup_and_exit(int sig) {
    (void)sig;
    for (int s = 0; s < MAX_SLOTS; s++) {
        int fd = g_slots[s].usb_fd;
        if (fd >= 0) {
            struct usb_fs_stop  st; memset(&st,0,sizeof(st));
            st.ep_index=0; ioctl(fd,USB_FS_STOP,&st);
            st.ep_index=1; ioctl(fd,USB_FS_STOP,&st);
            struct usb_fs_close fc; memset(&fc,0,sizeof(fc));
            fc.ep_index=0; ioctl(fd,USB_FS_CLOSE,&fc);
            fc.ep_index=1; ioctl(fd,USB_FS_CLOSE,&fc);
            struct usb_fs_uninit un; memset(&un,0,sizeof(un));
            ioctl(fd,USB_FS_UNINIT,&un);
            close(fd);
            g_slots[s].usb_fd = -1;
        }
        if (g_slots[s].handle >= 0)
            scePadVirtualDeviceDeleteDevice(g_slots[s].handle);
    }
    _exit(0);
}

int main(void) {
    int32_t userId=-1, fgUser=-1; int ret;

    ghostpad_status_log_reset();
    gp_log("Ghost-Control 定制版：小鸡启明星二代 VID 0x0e6f PID 0x0184\n", MAX_SLOTS);
    notify("Ghost-Control 小鸡启明星二代定制版");

    { int pfd=open(PID_PATH,O_RDONLY);
      if(pfd>=0){char pb[16]={0};read(pfd,pb,15);close(pfd);
        pid_t old=(pid_t)atoi(pb);
        if(old>0&&old!=getpid()){gp_log("Killing prev pid=%d\n",old);kill(old,SIGTERM);usleep(1200000);}
      }
      int pfd2=open(PID_PATH,O_WRONLY|O_CREAT|O_TRUNC,0600);
      if(pfd2>=0){char pb[16];snprintf(pb,sizeof(pb),"%d",getpid());write(pfd2,pb,strlen(pb));close(pfd2);}
    }

    for (int s = 0; s < MAX_SLOTS; s++) {
        g_slots[s].handle     = -1;
        g_slots[s].vdi_ready  = 0;
        g_slots[s].usb_active = 0;
        g_slots[s].release_requested = 0;
        g_slots[s].release_wait_neutral = 0;
        g_slots[s].confirmed  = 0;
        g_slots[s].usb_fd     = -1;
        g_slots[s].virtual_dev_id = 0;
        g_slots[s].dev_path[0]= '\0';
    }
    g_assign_slot = -1;

    signal(SIGTERM, cleanup_and_exit);
    signal(SIGINT,  cleanup_and_exit);

    sceUserServiceInitialize(NULL);
    sceUserServiceGetInitialUser(&userId);
    sceUserServiceGetForegroundUser(&fgUser);
    gp_log("userId=0x%08x fgUser=0x%08x\n", (uint32_t)userId, (uint32_t)fgUser);
    g_inject_uid = (fgUser > 0) ? fgUser : userId;
    if ((uint32_t)userId<0x10000000u||(uint32_t)userId>0x1000000Fu) userId=0x10000000;
    gp_log("inject_uid=0x%08x\n", (uint32_t)g_inject_uid);

    elevate_credentials();

    ret=scePadInit(); gp_log("scePadInit: 0x%08x\n", ret);
    ret=scePadSetProcessPrivilege(1); gp_log("scePadSetProcessPrivilege: 0x%08x\n", ret);

    for (int dh=0; dh<64; dh++) {
        if (scePadVirtualDeviceDeleteDevice(dh)==0) gp_log("deleteDevice(%d)\n", dh);
    }

    pthread_t klog_tid;
    if (pthread_create(&klog_tid, NULL, klog_capture_thread, NULL)==0) {
        pthread_detach(klog_tid);
        gp_log("klog thread started\n");
    }
    usleep(300000);

    pthread_t mgr_tid;
    if (pthread_create(&mgr_tid, NULL, controller_manager_thread, NULL)==0) {
        pthread_detach(mgr_tid);
        gp_log("Manager thread started\n");
    }

    uint32_t tick = 0;
    while (1) {
        usleep(1000000);
        tick++;
        if (tick % 10 == 0) {
            int active = 0;
            for (int s = 0; s < MAX_SLOTS; s++) if (g_slots[s].usb_active) active++;
            gp_log("alive tick=%u active_slots=%d\n", tick, active);
        }
    }
    return 0;
}
