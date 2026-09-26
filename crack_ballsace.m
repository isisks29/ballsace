// crack_ballsace.m
// 还原 blue.dylib 破解手法 (Ghidra 反编译确认: 502函数, 7层攻击链)
// IPA 破解版分析确认 (球球大作战_19.6.5):
//   - 注入方式: 主二进制硬编码 @executable_path/blue.dylib, 通过 dlopen 加载
//   - 目标 dylib: knmdbpjwfw.dylib (老版本, 17MB), 不是新版本 ballsace.dylib (3.9MB)
//   - 偏移量 0xcb09e8/0x80/0xc8 针对老版本 knmdbpjwfw.dylib
//   - blue.dylib constructor 在 dlopen 时执行, 延迟后安装所有 hook
//
// 编译命令 (GitHub Actions macos-latest):
// xcrun clang -target arm64-apple-ios15.0 \
//   -isysroot "$(xcrun --sdk iphoneos --show-sdk-path)" \
//   -dynamiclib -fobjc-arc \
//   -framework UIKit -framework Foundation -framework CoreGraphics \
//   -o crack_ballsace.dylib crack_ballsace.m
//
// 攻击链:
//   第0层: 反反调试/反注入 (hook 检测类, ReturnNO/NoopProtectionObject)
//   第1层: 远程开关 (RSA kill-switch, 简化为本地开关)
//   第2层: 网络层 (fishhook: connect/send/recv/close + method: NSURLSession/NSURLConnection/NSData)
//   第3层: 数据解析层 (JSONObjectWithData 篡改 + NSString/NSDictionary/AES 追踪)
//   第4层: UI 层 (BypassPresentViewController 拦截弹窗 + BypassLabelSetText 监控清理 + 悬浮球管理)
//   第5层: 验证状态伪造 (PrimeVerificationSuccessObject 直接内存写入 + ReturnNO + NoopProtectionObject)
//   第6层: 游戏作弊偏移管理 (GWorld/ActorArray, 与破解无关但存在)

#import <UIKit/UIKit.h>
#import <objc/runtime.h>
#import <objc/message.h>
#import <sys/socket.h>
#import <mach-o/dyld.h>
#import <mach-o/loader.h>
#import <mach-o/nlist.h>
#import <dlfcn.h>
#import <pthread.h>
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wdeprecated-declarations"

#pragma mark - ============ fishhook 精简实现 (Facebook fishhook, 内嵌) ============

struct rebinding {
    const char *name;
    void *replacement;
    void **replaced;
};

struct rebindings_entry {
    struct rebinding *rebindings;
    size_t rebindings_nel;
    struct rebindings_entry *next;
};

static struct rebindings_entry *_rebindings_head = NULL;

static int prepend_rebindings(struct rebindings_entry **head, struct rebinding rebindings[], size_t nel) {
    struct rebindings_entry *entry = (struct rebindings_entry *)malloc(sizeof(struct rebindings_entry));
    if (!entry) return -1;
    entry->rebindings = (struct rebinding *)malloc(sizeof(struct rebinding) * nel);
    if (!entry->rebindings) { free(entry); return -1; }
    memcpy(entry->rebindings, rebindings, sizeof(struct rebinding) * nel);
    entry->rebindings_nel = nel;
    entry->next = *head;
    *head = entry;
    return 0;
}

static void perform_rebinding_with_section(struct rebindings_entry *entry,
                                             const struct section_64 *section,
                                             intptr_t slide,
                                             const struct nlist_64 *symtab,
                                             const char *strtab,
                                             uint32_t *indirect_symtab) {
    uint32_t *indirect_symbol_indices = indirect_symtab + section->reserved1;
    void **indirect_symbol_bindings = (void **)((uintptr_t)slide + section->addr);
    for (uint i = 0; i < section->size / sizeof(void *); i++) {
        uint32_t symtab_index = indirect_symbol_indices[i];
        if (symtab_index == INDIRECT_SYMBOL_ABS || symtab_index == INDIRECT_SYMBOL_LOCAL) continue;
        uint32_t strtab_offset = symtab[symtab_index].n_un.n_strx;
        char *symbol_name = (char *)(strtab + strtab_offset);
        if (symbol_name[0] == '_') symbol_name++;
        for (struct rebindings_entry *e = entry; e; e = e->next) {
            for (size_t j = 0; j < e->rebindings_nel; j++) {
                if (strcmp(e->rebindings[j].name, symbol_name) == 0) {
                    if (e->rebindings[j].replaced) {
                        *e->rebindings[j].replaced = indirect_symbol_bindings[i];
                    }
                    indirect_symbol_bindings[i] = e->rebindings[j].replacement;
                }
            }
        }
    }
}

static void rebind_symbols_for_image(struct rebindings_entry *entry,
                                       const struct mach_header_64 *header,
                                       intptr_t slide) {
    Dl_info info;
    if (dladdr(header, &info) == 0) return;
    const struct segment_command_64 *linkedit_segment = NULL;
    const struct symtab_command *symtab_cmd = NULL;
    const struct dysymtab_command *dysymtab_cmd = NULL;
    struct load_command *lc = (struct load_command *)(header + 1);
    for (uint32_t i = 0; i < header->ncmds; i++, lc = (struct load_command *)((uintptr_t)lc + lc->cmdsize)) {
        if (lc->cmd == LC_SEGMENT_64) {
            struct segment_command_64 *seg = (struct segment_command_64 *)lc;
            if (strcmp(seg->segname, SEG_LINKEDIT) == 0) linkedit_segment = seg;
        } else if (lc->cmd == LC_SYMTAB) {
            symtab_cmd = (struct symtab_command *)lc;
        } else if (lc->cmd == LC_DYSYMTAB) {
            dysymtab_cmd = (struct dysymtab_command *)lc;
        }
    }
    if (!linkedit_segment || !symtab_cmd || !dysymtab_cmd) return;
    uintptr_t linkedit_base = (uintptr_t)slide + linkedit_segment->vmaddr - linkedit_segment->fileoff;
    const struct nlist_64 *symtab = (const struct nlist_64 *)(linkedit_base + symtab_cmd->symoff);
    const char *strtab = (const char *)(linkedit_base + symtab_cmd->stroff);
    uint32_t *indirect_symtab = (uint32_t *)(linkedit_base + dysymtab_cmd->indirectsymoff);
    lc = (struct load_command *)(header + 1);
    for (uint32_t i = 0; i < header->ncmds; i++, lc = (struct load_command *)((uintptr_t)lc + lc->cmdsize)) {
        if (lc->cmd == LC_SEGMENT_64) {
            struct segment_command_64 *seg = (struct segment_command_64 *)lc;
            struct section_64 *sect = (struct section_64 *)(seg + 1);
            for (uint32_t j = 0; j < seg->nsects; j++, sect++) {
                if (sect->flags & S_SYMBOL_STUBS &&
                    (sect->reserved1 == dysymtab_cmd->iundefsym ||
                     (sect->reserved1 >= dysymtab_cmd->iundefsym &&
                      sect->reserved1 < dysymtab_cmd->iundefsym + dysymtab_cmd->nundefsym))) {
                    perform_rebinding_with_section(entry, sect, slide, symtab, strtab, indirect_symtab);
                }
            }
        }
    }
}

static void rebind_symbols_image(const struct mach_header *header, intptr_t slide) {
    rebind_symbols_for_image(_rebindings_head, (const struct mach_header_64 *)header, slide);
}

static int rebind_symbols(struct rebinding rebindings[], size_t nel) {
    int ret = prepend_rebindings(&_rebindings_head, rebindings, nel);
    if (ret < 0) return ret;
    for (uint32_t i = 0; i < _dyld_image_count(); i++) {
        rebind_symbols_for_image(_rebindings_head,
                                   (const struct mach_header_64 *)_dyld_get_image_header(i),
                                   _dyld_get_image_vmaddr_slide(i));
    }
    _dyld_register_func_for_add_image(rebind_symbols_image);
    return 0;
}

#pragma mark - ============ 全局原始函数指针 ============

static IMP gOriginalPresentViewController = NULL;
static IMP gOriginalLabelSetText = NULL;
static IMP gOriginalAddSubview = NULL;
static IMP gOriginalViewDidAppear = NULL;
static IMP gOriginalJSONObjectWithData = NULL;
static IMP gOriginalNetworkManagerPost = NULL;

// fishhook 原始函数
static int (*orig_connect)(int, const struct sockaddr *, socklen_t) = NULL;
static ssize_t (*orig_send)(int, const void *, size_t, int) = NULL;
static ssize_t (*orig_recv)(int, void *, size_t, int) = NULL;
static int (*orig_close)(int) = NULL;

// 状态
static BOOL gProtectionHooksInstalled = NO;
static BOOL gOriginalHooksInstalled = NO;
static BOOL gNetworkManagerHookInstalled = NO;
static int gHookRetryCount = 0;

#pragma mark - ============ 第5层: 通用替换函数 ============

static BOOL ReturnNO(id self, SEL _cmd) {
    // Ghidra: ReturnNO @0x15760 (124字节)
    // 反编译确认: 不仅返回 NO, 还会记录被 hook 的方法名
    NSLog(@"[BypassHook] %@ -> NO", NSStringFromSelector(_cmd));
    return NO;
}

static id NoopProtectionObject(id self, SEL _cmd, id arg) {
    // Ghidra: NoopProtectionObject @0x1569c (140字节)
    // 反编译确认: 接受一个参数, 记录日志, 空操作返回 nil
    NSLog(@"[BypassHook] noop protection selector: %@ arg: %@", NSStringFromSelector(_cmd), arg);
    return nil;
}

#pragma mark - ============ 第5层: PrimeVerificationSuccessObject (直接内存写入, Ghidra确认) ============

// Ghidra 反编译确认 (blue.dylib @0x144f4, 456字节):
//   PrimeVerificationSuccessObject 不是方法调用, 是直接内存写入!
//   修改目标 dylib 验证对象的硬编码偏移量:
//     gTargetBase + 0xcb09e8  -> 验证对象二级指针 (long **)
//     verifyObj + 0x80        -> 状态字符串, 设为 "FW" (解释"无视破解FW插件")
//     verifyObj + 0xc8        -> 到期时间戳 (double), 设为 当前时间+315360000秒(10年)
//     gTargetBase + 0xcb09e0  -> 验证状态标志 (int), 设为 0
//   这些偏移量来自 blue.dylib, 针对老版本 knmdbpjwfw.dylib (17MB).
//   新版本 ballsace.dylib (3.9MB) 类名全部混淆, 偏移量可能不同, 需要重新分析.

#import <mach/vm_statistics.h>
#import <mach/mach_init.h>

// 偏移量配置 (针对老版本 knmdbpjwfw.dylib)
#define OFFSET_VERIFY_OBJ_PTR   0xcb09e8  // 验证对象二级指针
#define OFFSET_VERIFY_STATE      0xcb09e0  // 验证状态标志 (int)
#define OFFSET_VERIFY_STATUS_STR 0x80      // 验证对象内: 状态字符串偏移
#define OFFSET_VERIFY_EXPIRE     0xc8      // 验证对象内: 到期时间偏移 (double)
#define VERIFY_EXPIRE_YEARS      315360000.0  // 10年秒数 (DAT_00018400 = 315360000.0)

static uintptr_t gTargetBase = 0;

static uintptr_t FindTargetDylibBase(void) {
    // 通过 dyld 查找目标 dylib 的基地址
    for (uint32_t i = 0; i < _dyld_image_count(); i++) {
        const char *name = _dyld_get_image_name(i);
        if (!name) continue;
        NSString *imageName = [NSString stringWithUTF8String:name];
        if (!imageName) continue;
        // 匹配 ballsace 相关 dylib
        if ([imageName containsString:@"ballsace"] || [imageName containsString:@"BallsAce"] ||
            [imageName containsString:@"knmdb"] || [imageName containsString:@"cheat"]) {
            uintptr_t base = (uintptr_t)_dyld_get_image_header(i);
            NSLog(@"[BypassHook] FindTargetDylibBase: found %@ at 0x%lx", imageName, (unsigned long)base);
            return base;
        }
    }
    return 0;
}

static BOOL WriteTargetBytes(uintptr_t addr, const void *bytes, size_t len) {
    // Ghidra: WriteTargetBytes @0x149e0
    // 修改内存保护后写入
    kern_return_t kr = vm_protect(mach_task_self(), (vm_address_t)addr, (vm_size_t)len, NO, VM_PROT_READ | VM_PROT_WRITE);
    if (kr != KERN_SUCCESS) {
        NSLog(@"[BypassHook] WriteTargetBytes: vm_protect failed at 0x%lx: %d", (unsigned long)addr, kr);
        return NO;
    }
    memcpy((void *)addr, bytes, len);
    // 恢复只读保护
    vm_protect(mach_task_self(), (vm_address_t)addr, (vm_size_t)len, NO, VM_PROT_READ);
    return YES;
}

static void PrimeVerificationSuccessObject(void) {
    // Ghidra: PrimeVerificationSuccessObject @0x144f4 (456字节)
    // 直接内存写入, 修改验证对象的特定偏移量

    if (gTargetBase == 0) {
        gTargetBase = FindTargetDylibBase();
    }
    if (gTargetBase == 0) {
        NSLog(@"[BypassHook] PrimeVerificationSuccessObject: target base not found, skip");
        return;
    }

    // 读取验证对象二级指针: gTargetBase + 0xcb09e8
    uintptr_t verifyObjPtrAddr = gTargetBase + OFFSET_VERIFY_OBJ_PTR;
    uintptr_t verifyObjPtr = 0;
    memcpy(&verifyObjPtr, (const void *)verifyObjPtrAddr, sizeof(uintptr_t));
    if (verifyObjPtr == 0) {
        NSLog(@"[BypassHook] PrimeVerificationSuccessObject: verify object pointer is NULL");
        return;
    }

    // 解引用获取验证对象
    uintptr_t verifyObj = 0;
    memcpy(&verifyObj, (const void *)verifyObjPtr, sizeof(uintptr_t));
    if (verifyObj == 0) {
        NSLog(@"[BypassHook] PrimeVerificationSuccessObject: verify object is NULL");
        return;
    }

    NSLog(@"[BypassHook] PrimeVerificationSuccessObject: verifyObj=0x%lx", (unsigned long)verifyObj);

    // 1. verifyObj + 0x80 = "FW" (状态字符串)
    const char *fwStr = "FW";
    WriteTargetBytes(verifyObj + OFFSET_VERIFY_STATUS_STR, fwStr, 3);

    // 2. verifyObj + 0xc8 = 到期时间戳 = 当前时间 + 10年 (double)
    NSTimeInterval now = [[NSDate date] timeIntervalSince1970];
    double expireTime = now + VERIFY_EXPIRE_YEARS;
    WriteTargetBytes(verifyObj + OFFSET_VERIFY_EXPIRE, &expireTime, sizeof(double));

    // 3. gTargetBase + 0xcb09e0 = 0 (验证状态标志, int)
    int zero = 0;
    WriteTargetBytes(gTargetBase + OFFSET_VERIFY_STATE, &zero, sizeof(int));

    NSLog(@"[BypassHook] PrimeVerificationSuccessObject: DONE (state=FW, expire=%.0f, stateFlag=0)", expireTime);
}

#pragma mark - ============ 第4层: UI 辅助函数 ============

static BOOL IsAlertController(id vc) {
    if (!vc) return NO;
    Class cls = [vc class];
    while (cls) {
        NSString *name = NSStringFromClass(cls);
        if ([name isEqualToString:@"UIAlertController"] || [name containsString:@"Alert"]) {
            return YES;
        }
        cls = class_getSuperclass(cls);
    }
    return NO;
}

static BOOL ShouldSuppressAlert(id vc) {
    // Ghidra: ShouldSuppressAlert @0x10c0c (504字节)
    // 反编译确认: 用两组关键词检测 title 和 message
    //   第一组 (3个): 验证/卡密/授权相关
    //   第二组 (3个): UDID/udid/设备相关
    if (!IsAlertController(vc)) return NO;
    NSString *title = @""; NSString *message = @"";
    @try { title = [vc valueForKey:@"title"] ?: @""; message = [vc valueForKey:@"message"] ?: @""; } @catch (NSException *e) {}

    // 第一组: 验证/卡密/授权 (Ghidra: 3个混淆字符串)
    NSArray *verifyKeywords = @[
        @"卡密", @"验证", @"授权", @"激活", @"到期", @"过期",
        @"license", @"verify", @"auth", @"activation", @"expire",
        @"未授权", @"未激活", @"无效", @"error", @"失败",
    ];
    // 第二组: UDID/设备 (Ghidra: UDID, udid, 1个混淆字符串)
    NSArray *udidKeywords = @[@"UDID", @"udid", @"设备", @"绑定", @"device"];

    for (NSString *kw in verifyKeywords) {
        if ([title localizedCaseInsensitiveContainsString:kw] || [message localizedCaseInsensitiveContainsString:kw]) {
            return YES;
        }
    }
    for (NSString *kw in udidKeywords) {
        if ([title localizedCaseInsensitiveContainsString:kw] || [message localizedCaseInsensitiveContainsString:kw]) {
            return YES;
        }
    }
    return NO;
}

static BOOL IsVerificationHudText(NSString *text) {
    // Ghidra: IsVerificationHudText @0x11190 (284字节)
    // 反编译确认: 4个关键词, 包括 "1970-01-01" (检测到期时间显示)
    if (!text || ![text isKindOfClass:[NSString class]] || text.length == 0) return NO;
    NSArray *keywords = @[
        @"验证", @"卡密", @"授权", @"license", @"verify", @"auth", @"激活",
        @"1970-01-01", @"到期", @"过期", @"expire",
    ];
    for (NSString *kw in keywords) { if ([text localizedCaseInsensitiveContainsString:kw]) return YES; }
    return NO;
}

static BOOL IsUDIDHudText(NSString *text) {
    // Ghidra: IsUDIDHudText @0x112b8 (296字节)
    // 反编译确认: 5个关键词 (UDID, udid, SU, S, 1个混淆字符串)
    if (!text || ![text isKindOfClass:[NSString class]] || text.length == 0) return NO;
    NSArray *keywords = @[@"UDID", @"udid", @"设备号", @"设备ID", @"device", @"uuid"];
    for (NSString *kw in keywords) { if ([text localizedCaseInsensitiveContainsString:kw]) return YES; }
    return NO;
}

#pragma mark - ============ 第4层: SweepUDIDPromptHuds (清理 UDID 提示) ============

@interface UIView (BypassSweep)
- (void)bypass_sweepSubviews;
@end

@implementation UIView (BypassSweep)
- (void)bypass_sweepSubviews {
    for (UIView *subview in self.subviews) {
        if ([subview isKindOfClass:[UILabel class]]) {
            UILabel *label = (UILabel *)subview;
            if (IsUDIDHudText(label.text) || IsVerificationHudText(label.text)) {
                label.hidden = YES;
                NSLog(@"[BypassHook] SweepUDIDPromptHuds: hid label: %@", label.text);
            }
        }
        [subview bypass_sweepSubviews];
    }
}
@end

static void SweepUDIDPromptHuds(void) {
    // Ghidra: SweepUDIDPromptHuds @0x11484 (1120字节)
    dispatch_async(dispatch_get_main_queue(), ^{
        for (UIWindow *window in [[UIApplication sharedApplication] windows]) {
            [window.rootViewController.view bypass_sweepSubviews];
        }
    });
}

static void ScheduleUDIDPromptSweep(void) {
    // Ghidra: ScheduleUDIDPromptSweep @0x113ec
    dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(0.5 * NSEC_PER_SEC)),
                   dispatch_get_main_queue(), ^{ SweepUDIDPromptHuds(); });
}

#pragma mark - ============ 第4层: BypassPresentViewController (拦截卡密弹窗) ============

static void BypassPresentViewController(id self, SEL _cmd, id viewController, BOOL animated, void (^completion)(void)) {
    // Ghidra: BypassPresentViewController @0xfff4 (1436字节)
    // 核心: 检测到验证弹窗时直接调用 completion, 不实际展示
    if (ShouldSuppressAlert(viewController)) {
        NSString *title = @""; NSString *message = @"";
        @try { title = [viewController valueForKey:@"title"] ?: @""; message = [viewController valueForKey:@"message"] ?: @""; } @catch (NSException *e) {}
        NSLog(@"[BypassHook] suppress UIAlertController: title=%@ message=%@", title, message);
        if (completion) completion();
        PrimeVerificationSuccessObject();
        return;
    }
    if (gOriginalPresentViewController) {
        ((void(*)(id, SEL, id, BOOL, void(^)(void)))gOriginalPresentViewController)(self, _cmd, viewController, animated, completion);
    }
}

#pragma mark - ============ 第4层: BypassLabelSetText (监控文字+调度清理) ============

static void BypassLabelSetText(id self, SEL _cmd, NSString *text) {
    // Ghidra: BypassLabelSetText @0x10804 (272字节)
    // 注意: 不是直接改文字, 是先调用原始 setText, 然后监控文字变化
    if (gOriginalLabelSetText) {
        ((void(*)(id, SEL, NSString*))gOriginalLabelSetText)(self, _cmd, text);
    }
    if (IsVerificationHudText(text)) {
        NSLog(@"[BypassHook] verification HUD label text: %@", text);
    }
    if (IsUDIDHudText(text)) {
        NSLog(@"[BypassHook] UDID prompt label text: %@", text);
        ScheduleUDIDPromptSweep();
    }
}

#pragma mark - ============ 第4层: BypassAddSubview / BypassViewDidAppear ============

static void BypassAddSubview(id self, SEL _cmd, UIView *view) {
    if (gOriginalAddSubview) {
        ((void(*)(id, SEL, UIView*))gOriginalAddSubview)(self, _cmd, view);
    }
    if ([view isKindOfClass:[UILabel class]]) {
        UILabel *label = (UILabel *)view;
        if (IsUDIDHudText(label.text) || IsVerificationHudText(label.text)) {
            label.hidden = YES;
        }
    }
}

static void BypassViewDidAppear(id self, SEL _cmd, BOOL animated) {
    if (gOriginalViewDidAppear) {
        ((void(*)(id, SEL, BOOL))gOriginalViewDidAppear)(self, _cmd, animated);
    }
    dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(0.3 * NSEC_PER_SEC)),
                   dispatch_get_main_queue(), ^{ SweepUDIDPromptHuds(); });
}

#pragma mark - ============ 第4层: 悬浮球管理 ============

static void PromoteOriginalOverlay(void) {
    // Ghidra: PromoteOriginalOverlay @0x11cf8 (872字节)
    dispatch_async(dispatch_get_main_queue(), ^{
        NSArray *windows = [[UIApplication sharedApplication] windows];
        UIWindow *topWindow = [windows lastObject];
        if (topWindow) {
            [topWindow bringSubviewToFront:topWindow.rootViewController.view];
        }
        NSLog(@"[BypassHook] PromoteOriginalOverlay: overlay promoted");
    });
}

@interface NSObject (BypassConfigure)
- (void)bypass_configureInView:(UIView *)view;
@end

@implementation NSObject (BypassConfigure)
- (void)bypass_configureInView:(UIView *)view {
    if (!view) return;
    for (UIView *subview in view.subviews) {
        if ([subview isKindOfClass:[UILabel class]]) {
            UILabel *label = (UILabel *)subview;
            if (label.frame.size.width < 80 && label.frame.size.height < 80 && label.text.length > 0 && label.text.length < 10) {
                // 可能是悬浮球文字, 可在此修改为破解者标识
                // label.text = @"神叔免费";
            }
        }
        [self bypass_configureInView:subview];
    }
}
@end

static void ConfigureTargetImage(void) {
    // Ghidra: ConfigureTargetImage @0x13278 (1472字节)
    dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(3.0 * NSEC_PER_SEC)),
                   dispatch_get_main_queue(), ^{
        for (UIWindow *window in [[UIApplication sharedApplication] windows]) {
            [[NSObject new] bypass_configureInView:window.rootViewController.view];
        }
    });
}

#pragma mark - ============ 第3层: ReplacedJSONObjectWithData (JSON 篡改, 3108字节) ============

static id ReplacedJSONObjectWithData(id self, SEL _cmd, NSData *data, NSJSONReadingOptions opt, NSError **error) {
    // Ghidra: ReplacedJSONObjectWithData @0x6e00 (3108字节, 最大替换函数)
    if (!gOriginalJSONObjectWithData) {
        return [NSJSONSerialization JSONObjectWithData:data options:opt error:error];
    }
    id result = ((id(*)(id, SEL, NSData*, NSJSONReadingOptions, NSError**))gOriginalJSONObjectWithData)(self, _cmd, data, opt, error);
    if (![result isKindOfClass:[NSDictionary class]]) return result;

    NSDictionary *dict = (NSDictionary *)result;
    NSArray *verifyKeys = @[@"code", @"status", @"valid", @"expire", @"expired", @"license", @"auth", @"authorized", @"activated", @"message", @"msg", @"success"];
    BOOL isVerifyResponse = NO;
    for (NSString *key in verifyKeys) { if (dict[key] != nil) { isVerifyResponse = YES; break; } }
    if (!isVerifyResponse) return result;

    BOOL isFailure = NO;
    NSArray *failureValues = @[@"fail", @"failed", @"error", @"invalid", @"expired", @"unauthorized"];
    for (NSString *key in @[@"status", @"message", @"msg"]) {
        id val = dict[key];
        if ([val isKindOfClass:[NSString class]]) {
            for (NSString *fv in failureValues) {
                if ([(NSString *)val localizedCaseInsensitiveContainsString:fv]) { isFailure = YES; break; }
            }
        }
    }
    if ([dict[@"code"] isKindOfClass:[NSNumber class]] && [dict[@"code"] integerValue] != 0) isFailure = YES;
    if ([dict[@"valid"] isKindOfClass:[NSNumber class]] && ![dict[@"valid"] boolValue]) isFailure = YES;

    if (isFailure) {
        NSMutableDictionary *fakeResponse = [dict mutableCopy];
        fakeResponse[@"code"] = @0;
        fakeResponse[@"status"] = @"success";
        fakeResponse[@"valid"] = @YES;
        fakeResponse[@"authorized"] = @YES;
        fakeResponse[@"activated"] = @YES;
        fakeResponse[@"message"] = @"success";
        fakeResponse[@"expire"] = @"2099-12-31 23:59:59";
        fakeResponse[@"expired"] = @NO;
        NSLog(@"[BypassHook] ReplacedJSONObjectWithData: forged verify response (was failure)");
        return fakeResponse;
    }
    return result;
}

#pragma mark - ============ 第2层: fishhook 底层 socket 替换 ============

static int BypassConnect(int sockfd, const struct sockaddr *addr, socklen_t addrlen) {
    // Ghidra: ReplacedConnect @0xa404 (1300字节)
    if (orig_connect) return orig_connect(sockfd, addr, addrlen);
    return connect(sockfd, addr, addrlen);
}

static ssize_t BypassSend(int sockfd, const void *buf, size_t len, int flags) {
    // Ghidra: ReplacedSend @0xaa0c (2228字节)
    if (len > 0 && len < 4096) {
        NSLog(@"[BypassHook] BypassSend: %lu bytes", (unsigned long)len);
    }
    if (orig_send) return orig_send(sockfd, buf, len, flags);
    return send(sockfd, buf, len, flags);
}

static ssize_t BypassRecv(int sockfd, void *buf, size_t len, int flags) {
    if (orig_recv) return orig_recv(sockfd, buf, len, flags);
    return recv(sockfd, buf, len, flags);
}

static int BypassClose(int fd) {
    if (orig_close) return orig_close(fd);
    return close(fd);
}

#pragma mark - ============ 第0层: HookInstanceMethod / HookClassMethod (核心 hook 工具) ============

static void HookInstanceMethod(Class cls, SEL sel, IMP newImpl, IMP *origOut) {
    // Ghidra: HookInstanceMethod @0x15168 (104字节)
    // 反编译确认: class_getInstanceMethod -> method_getImplementation -> method_setImplementation
    if (!cls || !sel || !newImpl) return;
    Method method = class_getInstanceMethod(cls, sel);
    if (!method) return;
    IMP oldImpl = method_getImplementation(method);
    if (oldImpl == newImpl) return;
    if (origOut && *origOut == NULL) *origOut = oldImpl;
    method_setImplementation(method, newImpl);
}

static void HookClassMethod(Class cls, SEL sel, IMP newImpl, IMP *origOut) {
    // Ghidra: HookClassMethod @0x15bf4 (96字节)
    if (!cls || !sel || !newImpl) return;
    Method method = class_getClassMethod(cls, sel);
    if (!method) return;
    IMP oldImpl = method_getImplementation(method);
    if (oldImpl == newImpl) return;
    if (origOut && *origOut == NULL) *origOut = oldImpl;
    method_setImplementation(method, newImpl);
}

#pragma mark - ============ 第0层: InstallProtectionClassHooks (反反调试, 1888字节) ============

static void InstallProtectionClassHooks(void) {
    // Ghidra: InstallProtectionClassHooks @0x13a14 (1888字节, 最大hook安装函数)
    if (gProtectionHooksInstalled) return;

    // 1. hook 检测类 (混淆类名 _0x3F6A8E1C, Ghidra 确认)
    NSArray *detectionClassNames = @[
        @"_0x3F6A8E1C", @"DetectionManager", @"SecurityManager",
        @"AntiDebug", @"AntiTamper", @"JailbreakDetector",
    ];
    for (NSString *className in detectionClassNames) {
        Class cls = NSClassFromString(className);
        if (!cls) continue;
        NSLog(@"[BypassHook] InstallProtectionClassHooks: found detection class: %@", className);
        NSArray *detectionSelectors = @[
            @"performFullDetection", @"isJailbroken", @"detectInjectedLibraries",
            @"_0x7F2B4A6E", @"_0xA5C3E8D1",
            @"detectDebugger", @"isDebugged", @"checkIntegrity",
            @"verifySignature", @"isTampered", @"detectFrida",
            @"detectSubstrate", @"detectCydia",
        ];
        for (NSString *selName in detectionSelectors) {
            SEL sel = NSSelectorFromString(selName);
            if ([cls instancesRespondToSelector:sel]) HookInstanceMethod(cls, sel, (IMP)ReturnNO, NULL);
            if ([cls respondsToSelector:sel]) HookClassMethod(cls, sel, (IMP)ReturnNO, NULL);
        }
    }

    // 2. hook NetworkManager (Ghidra 确认: postEncryptedToPath:params:completion:)
    if (!gNetworkManagerHookInstalled) {
        Class netMgr = NSClassFromString(@"NetworkManager");
        SEL postSel = NSSelectorFromString(@"postEncryptedToPath:params:completion:");
        if (netMgr && postSel) {
            Method method = class_getInstanceMethod(netMgr, postSel);
            if (method) {
                gOriginalNetworkManagerPost = method_getImplementation(method);
                gNetworkManagerHookInstalled = YES;
                NSLog(@"[BypassHook] NetworkManager postEncrypted trace hook installed");
            }
        }
    }

    gProtectionHooksInstalled = YES;
    NSLog(@"[BypassHook] InstallProtectionClassHooks: protection hooks installed");
}

#pragma mark - ============ 第0层: InstallOriginalClassHooks ============

static void InstallOriginalClassHooks(void) {
    // Ghidra: InstallOriginalClassHooks @0x1393c (196字节)
    if (gOriginalHooksInstalled) return;
    NSArray *verifyClassNames = @[
        @"VerificationManager", @"LicenseManager", @"AuthManager",
        @"KamiManager", @"ActivationManager",
    ];
    NSArray *verifySelectors = @[
        @"verifyLicense:", @"verifyCode:", @"checkLicense", @"isLicenseValid",
        @"validateKey:", @"activateWithKey:", @"isActivated", @"isVerified", @"isAuthorized",
    ];
    for (NSString *className in verifyClassNames) {
        Class cls = NSClassFromString(className);
        if (!cls) continue;
        for (NSString *selName in verifySelectors) {
            SEL sel = NSSelectorFromString(selName);
            if ([cls instancesRespondToSelector:sel]) {
                HookInstanceMethod(cls, sel, (IMP)ReturnNO, NULL);
            }
        }
    }
    gOriginalHooksInstalled = YES;
    NSLog(@"[BypassHook] InstallOriginalClassHooks: original class hooks installed");
}

#pragma mark - ============ 第4层: InstallPresentationSwizzle ============

static void InstallPresentationSwizzle(void) {
    // Ghidra: InstallPresentationSwizzle @0xfdb8 (536字节)
    Class uiVC = NSClassFromString(@"UIViewController");
    if (uiVC) {
        HookInstanceMethod(uiVC, @selector(presentViewController:animated:completion:),
                           (IMP)BypassPresentViewController, &gOriginalPresentViewController);
        HookInstanceMethod(uiVC, @selector(viewDidAppear:),
                           (IMP)BypassViewDidAppear, &gOriginalViewDidAppear);
    }
    Class uiLabel = NSClassFromString(@"UILabel");
    if (uiLabel) {
        HookInstanceMethod(uiLabel, @selector(setText:),
                           (IMP)BypassLabelSetText, &gOriginalLabelSetText);
    }
    Class uiView = NSClassFromString(@"UIView");
    if (uiView) {
        HookInstanceMethod(uiView, @selector(addSubview:),
                           (IMP)BypassAddSubview, &gOriginalAddSubview);
    }
    Class jsonSer = NSClassFromString(@"NSJSONSerialization");
    if (jsonSer) {
        HookClassMethod(jsonSer, @selector(JSONObjectWithData:options:error:),
                        (IMP)ReplacedJSONObjectWithData, &gOriginalJSONObjectWithData);
    }
    NSLog(@"[BypassHook] InstallPresentationSwizzle: UI swizzles installed");
}

#pragma mark - ============ 第2层: InstallNetworkSwizzles (fishhook) ============

static void InstallNetworkSwizzles(void) {
    // Ghidra: InstallAuthorNetworkSwizzles @0x5b38 (2156字节)
    struct rebinding rebindings[] = {
        {"connect", (void *)BypassConnect, (void **)&orig_connect},
        {"send", (void *)BypassSend, (void **)&orig_send},
        {"recv", (void *)BypassRecv, (void **)&orig_recv},
        {"close", (void *)BypassClose, (void **)&orig_close},
    };
    rebind_symbols(rebindings, sizeof(rebindings) / sizeof(rebindings[0]));
    NSLog(@"[BypassHook] InstallNetworkSwizzles: fishhook socket functions installed");
}

#pragma mark - ============ 重试机制 ============

static void ScheduleOriginalClassHookRetries(void) {
    // Ghidra: ScheduleOriginalClassHookRetries @0x16294
    // 反编译确认: 先调 InstallOriginalClassHooks, 再调 InstallProtectionClassHooks
    if (gHookRetryCount >= 10) return;
    dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(1.0 * NSEC_PER_SEC)),
                   dispatch_get_main_queue(), ^{
        InstallOriginalClassHooks();
        InstallProtectionClassHooks();
        gHookRetryCount++;
        if (gHookRetryCount < 10) ScheduleOriginalClassHookRetries();
    });
}

#pragma mark - ============ dyld 监听 (ImageAdded) ============

static void ImageAdded(const struct mach_header *header, intptr_t slide) {
    // Ghidra: ImageAdded @0x5264 (260字节)
    const char *name = (const char *)_dyld_get_image_name((uint32_t)(intptr_t)header);
    if (!name) return;
    NSString *imageName = [NSString stringWithUTF8String:name];
    if (!imageName) return;
    NSArray *targetKeywords = @[@"ballsace", @"BallsAce", @"cheat", @"tweak", @"plugin"];
    for (NSString *kw in targetKeywords) {
        if ([imageName containsString:kw]) {
            NSLog(@"[BypassHook] ImageAdded: target dylib detected: %@", imageName);
            dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(0.5 * NSEC_PER_SEC)),
                           dispatch_get_main_queue(), ^{
                InstallProtectionClassHooks();
                InstallOriginalClassHooks();
            });
            break;
        }
    }
}

#pragma mark - ============ Constructor (Ra_xiNy_Init, 1540字节) ============

__attribute__((constructor))
static void Ra_xiNy_Init(void) {
    // Ghidra: Ra_xiNy_Init @0x4b78 (1540字节, constructor)
    NSLog(@"[BypassHook] Ra_xiNy_Init: crack dylib loaded (ballsace bypass)");

    // 第1层: 远程开关 (实际 blue.dylib 用 RSA 加密, 简化为始终启用)
    // 第2层: fishhook 底层 socket
    InstallNetworkSwizzles();
    // 第4层: UI swizzle
    InstallPresentationSwizzle();
    // 第0层: 反反调试 + 验证方法 hook
    InstallProtectionClassHooks();
    InstallOriginalClassHooks();
    // 第5层: 伪造验证成功对象
    PrimeVerificationSuccessObject();
    // 第4层: 悬浮球管理
    PromoteOriginalOverlay();
    ConfigureTargetImage();
    // 重试机制
    ScheduleOriginalClassHookRetries();
    // dyld 监听
    _dyld_register_func_for_add_image(ImageAdded);

    NSLog(@"[BypassHook] Ra_xiNy_Init: all hooks installed, bypass active");
}

#pragma clang diagnostic pop
