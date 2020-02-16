const std = @import("std");
const expectEqual = std.testing.expectEqual;
const expect = std.testing.expect;
const builtin = @import("builtin");
const panic = @import("../../panic.zig").panic;
const arch = @import("arch.zig");
const isr = @import("isr.zig");
const MemProfile = @import("../../mem.zig").MemProfile;
const tty = @import("../../tty.zig");
const log = @import("../../log.zig");
const mem = @import("../../mem.zig");
const vmm = @import("../../vmm.zig");
const multiboot = @import("../../multiboot.zig");
const options = @import("build_options");
const testing = std.testing;

/// An array of directory entries and page tables. Forms the first level of paging and covers the entire 4GB memory space.
pub const Directory = packed struct {
    /// The directory entries.
    entries: [ENTRIES_PER_DIRECTORY]DirectoryEntry,

    /// The tables allocated for the directory. This is ignored by the CPU.
    tables: [ENTRIES_PER_DIRECTORY]?*Table,
};

/// An array of table entries. Forms the second level of paging and covers a 4MB memory space.
const Table = packed struct {
    /// The table entries.
    entries: [ENTRIES_PER_TABLE]TableEntry,
};

/// All errors that can be thrown by paging functions.
const PagingError = error{
    /// Physical addresses are invalid (definition is up to the function).
    InvalidPhysAddresses,

    /// Virtual addresses are invalid (definition is up to the function).
    InvalidVirtAddresses,

    /// Physical and virtual addresses don't cover spaces of the same size.
    PhysicalVirtualMismatch,

    /// Physical addresses aren't aligned by page size.
    UnalignedPhysAddresses,

    /// Virtual addresses aren't aligned by page size.
    UnalignedVirtAddresses,
};

/// An entry within a directory. References a single page table.
/// Bit 0: Present. Set if present in physical memory.
///        When not set, all remaining 31 bits are ignored and available for use.
/// Bit 1: Writable. Set if writable.
/// Bit 2: User. Set if accessible by user mode.
/// Bit 3: Write through. Set if write-through caching is enabled.
/// Bit 4: Cache disabled. Set if caching is disabled for this table.
/// Bit 5: Accessed. Set by the CPU when the table is accessed. Not cleared by CPU.
/// Bit 6: Zero.
/// Bit 7: Page size. Set if this entry covers a single 4MB page rather than 1024 4KB pages.
/// Bit 8: Ignored.
/// Bits 9-11: Ignored and available for use by kernel.
/// Bits 12-31: The 4KB aligned physical address of the corresponding page table.
///             Must be 4MB aligned if the page size bit is set.
const DirectoryEntry = u32;

/// An entry within a page table. References a single page.
/// Bit 0: Present. Set if present in physical memory.
///        When not set, all remaining 31 bits are ignored and available for use.
/// Bit 1: Writable. Set if writable.
/// Bit 2: User. Set if accessible by user mode.
/// Bit 3: Write through. Set if write-through caching is enabled.
/// Bit 4: Cache disabled. Set if caching is disabled for this page.
/// Bit 5: Accessed. Set by the CPU when the page is accessed. Not cleared by CPU.
/// Bit 6: Dirty. Set by the CPU when the page has been written to. Not cleared by the CPU.
/// Bit 7: Zero.
/// Bit 8: Global. Set if the cached address for this page shouldn't be updated when cr3 is changed.
/// Bits 9-11: Ignored and available for use by the kernel.
/// Bits 12-31: The 4KB aligned physical address mapped to this page.
const TableEntry = u32;

/// Each directory has 1024 entries
const ENTRIES_PER_DIRECTORY: u32 = 1024;

/// Each table has 1024 entries
const ENTRIES_PER_TABLE: u32 = 1024;

/// There are 1024 entries per directory with each one covering 4KB
const PAGES_PER_DIR_ENTRY: u32 = 1024;

/// There are 1 million pages per directory
const PAGES_PER_DIR: u32 = ENTRIES_PER_DIRECTORY * PAGES_PER_DIR_ENTRY;

/// The bitmasks for the bits in a DirectoryEntry
const DENTRY_PRESENT: u32 = 0x1;
const DENTRY_WRITABLE: u32 = 0x2;
const DENTRY_USER: u32 = 0x4;
const DENTRY_WRITE_THROUGH: u32 = 0x8;
const DENTRY_CACHE_DISABLED: u32 = 0x10;
const DENTRY_ACCESSED: u32 = 0x20;
const DENTRY_ZERO: u32 = 0x40;
const DENTRY_4MB_PAGES: u32 = 0x80;
const DENTRY_IGNORED: u32 = 0x100;
const DENTRY_AVAILABLE: u32 = 0xE00;
const DENTRY_PAGE_ADDR: u32 = 0xFFFFF000;

/// The bitmasks for the bits in a TableEntry
const TENTRY_PRESENT: u32 = 0x1;
const TENTRY_WRITABLE: u32 = 0x2;
const TENTRY_USER: u32 = 0x4;
const TENTRY_WRITE_THROUGH: u32 = 0x8;
const TENTRY_CACHE_DISABLED: u32 = 0x10;
const TENTRY_ACCESSED: u32 = 0x20;
const TENTRY_DIRTY: u32 = 0x40;
const TENTRY_ZERO: u32 = 0x80;
const TENTRY_GLOBAL: u32 = 0x100;
const TENTRY_AVAILABLE: u32 = 0xE00;
const TENTRY_PAGE_ADDR: u32 = 0xFFFFF000;

/// The number of bytes in 4MB
pub const PAGE_SIZE_4MB: u32 = 0x400000;

/// The number of bytes in 4KB
pub const PAGE_SIZE_4KB: u32 = PAGE_SIZE_4MB / 1024;

/// The kernel's page directory. Should only be used to map kernel-owned code and data
pub var kernel_directory: Directory align(@truncate(u29, PAGE_SIZE_4KB)) = Directory{ .entries = [_]DirectoryEntry{0} ** ENTRIES_PER_DIRECTORY, .tables = [_]?*Table{null} ** ENTRIES_PER_DIRECTORY };

///
/// Convert a virtual address to an index within an array of directory entries.
///
/// Arguments:
///     IN virt: usize - The virtual address to convert.
///
/// Return: usize
///     The index into an array of directory entries.
///
inline fn virtToDirEntryIdx(virt: usize) usize {
    return (virt / PAGE_SIZE_4MB) % ENTRIES_PER_DIRECTORY;
}

///
/// Convert a virtual address to an index within an array of table entries.
///
/// Arguments:
///     IN virt: usize - The virtual address to convert.
///
/// Return: usize
///     The index into an array of table entries.
///
inline fn virtToTableEntryIdx(virt: usize) usize {
    return (virt / PAGE_SIZE_4KB) % ENTRIES_PER_TABLE;
}

///
/// Set the bit(s) associated with an attribute of a table or directory entry.
///
/// Arguments:
///     val: *align(1) u32 - The entry to modify
///     attr: u32 - The bits corresponding to the atttribute to set
///
inline fn setAttribute(val: *align(1) u32, attr: u32) void {
    val.* |= attr;
}

///
/// Clear the bit(s) associated with an attribute of a table or directory entry.
///
/// Arguments:
///     val: *align(1) u32 - The entry to modify
///     attr: u32 - The bits corresponding to the atttribute to clear
///
inline fn clearAttribute(val: *align(1) u32, attr: u32) void {
    val.* &= ~attr;
}

///
/// Map a page directory entry, setting the present, size, writable, write-through and physical address bits.
/// Clears the user and cache disabled bits. Entry should be zero'ed.
///
/// Arguments:
///     OUT dir: *Directory - The directory that this entry is in
///     IN virt_addr: usize - The start of the virtual space to map
///     IN virt_end: usize - The end of the virtual space to map
///     IN phys_addr: usize - The start of the physical space to map
///     IN phys_end: usize - The end of the physical space to map
///     IN attrs: vmm.Attributes - The attributes to apply to this mapping
///     IN allocator: *Allocator - The allocator to use to map any tables needed
///
/// Error: PagingError || std.mem.Allocator.Error
///     PagingError.InvalidPhysAddresses - The physical start address is greater than the end.
///     PagingError.InvalidVirtAddresses - The virtual start address is greater than the end or is larger than 4GB.
///     PagingError.PhysicalVirtualMismatch - The differences between the virtual addresses and the physical addresses aren't the same.
///     PagingError.UnalignedPhysAddresses - One or both of the physical addresses aren't page size aligned.
///     PagingError.UnalignedVirtAddresses - One or both of the virtual addresses aren't page size aligned.
///     std.mem.Allocator.Error.* - See std.mem.Allocator.alignedAlloc.
///
fn mapDirEntry(dir: *Directory, virt_start: usize, virt_end: usize, phys_start: usize, phys_end: usize, attrs: vmm.Attributes, allocator: *std.mem.Allocator) (PagingError || std.mem.Allocator.Error)!void {
    if (phys_start > phys_end) {
        return PagingError.InvalidPhysAddresses;
    }
    if (virt_start > virt_end) {
        return PagingError.InvalidVirtAddresses;
    }
    if (phys_end - phys_start != virt_end - virt_start) {
        return PagingError.PhysicalVirtualMismatch;
    }
    if (!std.mem.isAligned(phys_start, PAGE_SIZE_4KB) or !std.mem.isAligned(phys_end, PAGE_SIZE_4KB)) {
        return PagingError.UnalignedPhysAddresses;
    }
    if (!std.mem.isAligned(virt_start, PAGE_SIZE_4KB) or !std.mem.isAligned(virt_end, PAGE_SIZE_4KB)) {
        return PagingError.UnalignedVirtAddresses;
    }

    const entry = virt_start / PAGE_SIZE_4MB;
    if (entry >= ENTRIES_PER_DIRECTORY)
        return PagingError.InvalidVirtAddresses;
    var dir_entry = &dir.entries[entry];

    setAttribute(dir_entry, DENTRY_PRESENT);
    setAttribute(dir_entry, DENTRY_WRITE_THROUGH);
    clearAttribute(dir_entry, DENTRY_4MB_PAGES);

    if (attrs.writable) {
        setAttribute(dir_entry, DENTRY_WRITABLE);
    } else {
        clearAttribute(dir_entry, DENTRY_WRITABLE);
    }

    if (attrs.kernel) {
        clearAttribute(dir_entry, DENTRY_USER);
    } else {
        setAttribute(dir_entry, DENTRY_USER);
    }

    if (attrs.cachable) {
        clearAttribute(dir_entry, DENTRY_CACHE_DISABLED);
    } else {
        setAttribute(dir_entry, DENTRY_CACHE_DISABLED);
    }

    // Only create a new table if one hasn't already been created for this dir entry.
    // Prevents us from overriding previous mappings.
    var table: *Table = undefined;
    if (dir.tables[entry]) |tbl| {
        table = tbl;
    } else {
        // Create a table and put the physical address in the dir entry
        table = &(try allocator.alignedAlloc(Table, @truncate(u29, PAGE_SIZE_4KB), 1))[0];
        @memset(@ptrCast([*]u8, table), 0, @sizeOf(Table));
        const table_phys_addr = @ptrToInt(mem.virtToPhys(table));
        dir_entry.* |= DENTRY_PAGE_ADDR & table_phys_addr;
        dir.tables[entry] = table;
    }

    // Map the table entries within the requested space
    var virt = virt_start;
    var phys = phys_start;
    var tentry = virtToTableEntryIdx(virt);
    while (virt < virt_end) : ({
        virt += PAGE_SIZE_4KB;
        phys += PAGE_SIZE_4KB;
        tentry += 1;
    }) {
        try mapTableEntry(&table.entries[tentry], phys);
    }
}

///
/// Map a table entry by setting its bits to the appropriate values.
/// Sets the entry to be present, writable, kernel access, write through, cache enabled, non-global and the page address bits.
///
/// Arguments:
///     OUT entry: *align(1) TableEntry - The entry to map. 1 byte aligned.
///     IN phys_addr: usize - The physical address to map the table entry to.
///
/// Error: PagingError
///     PagingError.UnalignedPhysAddresses - If the physical address isn't page size aligned.
///
fn mapTableEntry(entry: *align(1) TableEntry, phys_addr: usize) PagingError!void {
    if (!std.mem.isAligned(phys_addr, PAGE_SIZE_4KB)) {
        return PagingError.UnalignedPhysAddresses;
    }
    entry.* |= TENTRY_PRESENT;
    entry.* |= TENTRY_WRITABLE;
    entry.* &= ~TENTRY_USER;
    entry.* |= TENTRY_WRITE_THROUGH;
    entry.* &= ~TENTRY_CACHE_DISABLED;
    entry.* &= ~TENTRY_GLOBAL;
    entry.* |= TENTRY_PAGE_ADDR & phys_addr;
}

///
/// Map a page directory. The addresses passed must be page size aligned and be the same distance apart.
///
/// Arguments:
///     OUT entry: *Directory - The directory to map
///     IN virt_start: usize - The virtual address at which to start mapping
///     IN virt_end: usize - The virtual address at which to stop mapping
///     IN phys_start: usize - The physical address at which to start mapping
///     IN phys_end: usize - The physical address at which to stop mapping
///     IN attrs: vmm.Attributes - The attributes to apply to this mapping
///     IN allocator: *Allocator - The allocator to use to map any tables needed
///
/// Error: std.mem.Allocator.Error || PagingError
///     * - See mapDirEntry.
///
fn mapDir(dir: *Directory, virt_start: usize, virt_end: usize, phys_start: usize, phys_end: usize, attrs: vmm.Attributes, allocator: *std.mem.Allocator) (std.mem.Allocator.Error || PagingError)!void {
    var virt_addr = virt_start;
    var phys_addr = phys_start;
    var page = virt_addr / PAGE_SIZE_4KB;
    var entry_idx = virt_addr / PAGE_SIZE_4MB;
    while (entry_idx < ENTRIES_PER_DIRECTORY and virt_addr < virt_end) : ({
        phys_addr += PAGE_SIZE_4MB;
        virt_addr += PAGE_SIZE_4MB;
        entry_idx += 1;
    }) {
        try mapDirEntry(dir, virt_addr, std.math.min(virt_end, virt_addr + PAGE_SIZE_4MB), phys_addr, std.math.min(phys_end, phys_addr + PAGE_SIZE_4MB), attrs, allocator);
    }
}

///
/// Called when a page fault occurs.
///
/// Arguments:
///     IN state: *arch.InterruptContext - The CPU's state when the fault occurred.
///
fn pageFault(state: *arch.InterruptContext) void {
    @panic("Page fault");
}

///
/// Map a virtual region of memory to a physical region with a set of attributes within a directory.
/// If this call is made to a directory that has been loaded by the CPU, the virtual memory will immediately be accessible (given the proper attributes)
/// and will be mirrored to the physical region given. Otherwise it will be accessible once the given directory is loaded by the CPU.
///
/// This call will panic if mapDir returns an error when called with any of the arguments given.
///
/// Arguments:
///     IN virtual_start: usize - The start of the virtual region to map
///     IN virtual_end: usize - The end (exclusive) of the virtual region to map
///     IN physical_start: usize - The start of the physical region to mape to
///     IN physical_end: usize - The end (exclusive) of the physical region to map to
///     IN attrs: vmm.Attributes - The attributes to apply to this mapping
///     INOUT allocator: *std.mem.Allocator - The allocator to use to allocate any intermediate data structures required to map this region
///     INOUT dir: *Directory - The page directory to map within
///
pub fn map(virtual_start: usize, virtual_end: usize, physical_start: usize, physical_end: usize, attrs: vmm.Attributes, allocator: *std.mem.Allocator, dir: *Directory) void {
    mapDir(dir, virtual_start, virtual_end, physical_start, physical_end, attrs, allocator) catch |e| panic(@errorReturnTrace(), "Failed to map virtual {x} -> {x} to physical {x} -> {x}: {}", .{ virtual_start, virtual_end, physical_start, physical_end, e });
}

///
/// Unmap a virtual region of memory within a directory so that it is no longer accessible.
///
/// Arguments:
///     IN virtual_start: usize - The start of the virtual region to unmap
///     IN virtual_end: usize - The end (exclusive) of the virtual region to unmap
///     INOUT dir: *Directory - The page directory to unmap within
///
pub fn unmap(virtual_start: usize, virtual_end: usize, dir: *Directory) void {
    // TODO: Implement
}

///
/// Initialise x86 paging, overwriting any previous paging set up.
///
/// Arguments:
///     IN mem_profile: *const MemProfile - The memory profile of the system and kernel
///     IN allocator: *std.mem.Allocator - The allocator to use
///
pub fn init(mb_info: *multiboot.multiboot_info_t, mem_profile: *const MemProfile, allocator: *std.mem.Allocator) void {
    log.logInfo("Init paging\n", .{});

    isr.registerIsr(isr.PAGE_FAULT, if (options.rt_test) rt_pageFault else pageFault) catch |e| {
        panic(@errorReturnTrace(), "Failed to register page fault ISR: {}\n", .{e});
    };
    const dir_physaddr = @ptrToInt(mem.virtToPhys(&kernel_directory));
    asm volatile ("mov %[addr], %%cr3"
        :
        : [addr] "{eax}" (dir_physaddr)
    );
    log.logInfo("Done\n", .{});

    const v_end = std.mem.alignForward(@ptrToInt(mem_profile.vaddr_end) + mem_profile.fixed_alloc_size, PAGE_SIZE_4KB);
    if (options.rt_test) runtimeTests(v_end);
}

fn checkDirEntry(entry: DirectoryEntry, virt_start: usize, virt_end: usize, phys_start: usize, attrs: vmm.Attributes, table: *Table) void {
    expectEqual(entry & DENTRY_PRESENT, DENTRY_PRESENT);
    expectEqual(entry & DENTRY_WRITABLE, if (attrs.writable) DENTRY_WRITABLE else 0);
    expectEqual(entry & DENTRY_USER, if (attrs.kernel) 0 else DENTRY_USER);
    expectEqual(entry & DENTRY_WRITE_THROUGH, DENTRY_WRITE_THROUGH);
    expectEqual(entry & DENTRY_CACHE_DISABLED, if (attrs.cachable) 0 else DENTRY_CACHE_DISABLED);
    expectEqual(entry & DENTRY_4MB_PAGES, 0);
    expectEqual(entry & DENTRY_ZERO, 0);

    var tentry_idx = virtToTableEntryIdx(virt_start);
    var tentry_idx_end = virtToTableEntryIdx(virt_end);
    var phys = phys_start;
    while (tentry_idx < tentry_idx_end) : ({
        tentry_idx += 1;
        phys += PAGE_SIZE_4KB;
    }) {
        const tentry = table.entries[tentry_idx];
        checkTableEntry(tentry, phys, attrs);
    }
}

fn checkTableEntry(entry: TableEntry, page_phys: usize, attrs: vmm.Attributes) void {
    expect(entry & TENTRY_PRESENT != 0);
    expectEqual(entry & TENTRY_WRITABLE, if (attrs.writable) TENTRY_WRITABLE else 0);
    expectEqual(entry & TENTRY_USER, if (attrs.kernel) 0 else TENTRY_USER);
    expectEqual(entry & TENTRY_WRITE_THROUGH, TENTRY_WRITE_THROUGH);
    expectEqual(entry & TENTRY_CACHE_DISABLED, if (attrs.cachable) 0 else TENTRY_CACHE_DISABLED);
    expectEqual(entry & TENTRY_ZERO, 0);
    expectEqual(entry & TENTRY_GLOBAL, 0);
    expectEqual(entry & TENTRY_PAGE_ADDR, page_phys);
}

test "setAttribute and clearAttribute" {
    var val: u32 = 0;
    const attrs = [_]u32{ DENTRY_PRESENT, DENTRY_WRITABLE, DENTRY_USER, DENTRY_WRITE_THROUGH, DENTRY_CACHE_DISABLED, DENTRY_ACCESSED, DENTRY_ZERO, DENTRY_4MB_PAGES, DENTRY_IGNORED, DENTRY_AVAILABLE, DENTRY_PAGE_ADDR };

    for (attrs) |attr| {
        const old_val = val;
        setAttribute(&val, attr);
        std.testing.expectEqual(val, old_val | attr);
    }

    for (attrs) |attr| {
        const old_val = val;
        clearAttribute(&val, attr);
        std.testing.expectEqual(val, old_val & ~attr);
    }
}

test "virtToDirEntryIdx" {
    expectEqual(virtToDirEntryIdx(0), 0);
    expectEqual(virtToDirEntryIdx(123), 0);
    expectEqual(virtToDirEntryIdx(PAGE_SIZE_4MB - 1), 0);
    expectEqual(virtToDirEntryIdx(PAGE_SIZE_4MB), 1);
    expectEqual(virtToDirEntryIdx(PAGE_SIZE_4MB + 1), 1);
    expectEqual(virtToDirEntryIdx(PAGE_SIZE_4MB * 2), 2);
    expectEqual(virtToDirEntryIdx(PAGE_SIZE_4MB * (ENTRIES_PER_DIRECTORY - 1)), ENTRIES_PER_DIRECTORY - 1);
}

test "virtToTableEntryIdx" {
    expectEqual(virtToTableEntryIdx(0), 0);
    expectEqual(virtToTableEntryIdx(123), 0);
    expectEqual(virtToTableEntryIdx(PAGE_SIZE_4KB - 1), 0);
    expectEqual(virtToTableEntryIdx(PAGE_SIZE_4KB), 1);
    expectEqual(virtToTableEntryIdx(PAGE_SIZE_4KB + 1), 1);
    expectEqual(virtToTableEntryIdx(PAGE_SIZE_4KB * 2), 2);
    expectEqual(virtToTableEntryIdx(PAGE_SIZE_4KB * (ENTRIES_PER_TABLE - 1)), ENTRIES_PER_TABLE - 1);
    expectEqual(virtToTableEntryIdx(PAGE_SIZE_4KB * (ENTRIES_PER_TABLE)), 0);
}

test "mapDirEntry" {
    var allocator = std.heap.direct_allocator;
    var dir: Directory = Directory{ .entries = [_]DirectoryEntry{0} ** ENTRIES_PER_DIRECTORY, .tables = [_]?*Table{null} ** ENTRIES_PER_DIRECTORY };
    var phys: usize = 0 * PAGE_SIZE_4MB;
    const phys_end: usize = phys + PAGE_SIZE_4MB;
    const virt: usize = 1 * PAGE_SIZE_4MB;
    const virt_end: usize = virt + PAGE_SIZE_4MB;
    try mapDirEntry(&dir, virt, virt_end, phys, phys_end, .{ .kernel = true, .writable = true, .cachable = true }, allocator);

    const entry_idx = virtToDirEntryIdx(virt);
    const entry = dir.entries[entry_idx];
    const table = dir.tables[entry_idx] orelse unreachable;
    checkDirEntry(entry, virt, virt_end, phys, .{ .kernel = true, .writable = true, .cachable = true }, table);
}

test "mapDirEntry returns errors correctly" {
    var allocator = std.heap.direct_allocator;
    var dir = Directory{ .entries = [_]DirectoryEntry{0} ** ENTRIES_PER_DIRECTORY, .tables = undefined };
    const attrs = vmm.Attributes{ .kernel = true, .writable = true, .cachable = true };
    testing.expectError(PagingError.UnalignedVirtAddresses, mapDirEntry(&dir, 1, PAGE_SIZE_4KB + 1, 0, PAGE_SIZE_4KB, attrs, allocator));
    testing.expectError(PagingError.UnalignedPhysAddresses, mapDirEntry(&dir, 0, PAGE_SIZE_4KB, 1, PAGE_SIZE_4KB + 1, attrs, allocator));
    testing.expectError(PagingError.PhysicalVirtualMismatch, mapDirEntry(&dir, 0, PAGE_SIZE_4KB, 1, PAGE_SIZE_4KB, attrs, allocator));
    testing.expectError(PagingError.InvalidVirtAddresses, mapDirEntry(&dir, 1, 0, 0, PAGE_SIZE_4KB, attrs, allocator));
    testing.expectError(PagingError.InvalidPhysAddresses, mapDirEntry(&dir, 0, PAGE_SIZE_4KB, 1, 0, attrs, allocator));
}

test "mapDir" {
    var allocator = std.heap.direct_allocator;
    var dir = Directory{ .entries = [_]DirectoryEntry{0} ** ENTRIES_PER_DIRECTORY, .tables = [_]?*Table{null} ** ENTRIES_PER_DIRECTORY };
    const phys_start: usize = PAGE_SIZE_4MB * 2;
    const virt_start: usize = PAGE_SIZE_4MB * 4;
    const phys_end: usize = PAGE_SIZE_4MB * 4;
    const virt_end: usize = PAGE_SIZE_4MB * 6;
    const attrs = vmm.Attributes{ .kernel = true, .writable = true, .cachable = true };
    mapDir(&dir, virt_start, virt_end, phys_start, phys_end, attrs, allocator) catch unreachable;

    var virt = virt_start;
    var phys = phys_start;
    while (virt < virt_end) : ({
        virt += PAGE_SIZE_4MB;
        phys += PAGE_SIZE_4MB;
    }) {
        const entry_idx = virtToDirEntryIdx(virt);
        const entry = dir.entries[entry_idx];
        const table = dir.tables[entry_idx] orelse unreachable;
        checkDirEntry(entry, virt, virt + PAGE_SIZE_4MB, phys, attrs, table);
    }
}

// The labels to jump to after attempting to cause a page fault. This is needed as we don't want to cause an
// infinite loop by jummping to the same instruction that caused the fault.
extern var rt_fault_callback: *u32;
extern var rt_fault_callback2: *u32;

var faulted = false;
var use_callback2 = false;

fn rt_pageFault(ctx: *arch.InterruptContext) void {
    faulted = true;
    // Return to the fault callback
    ctx.eip = @ptrToInt(&if (use_callback2) rt_fault_callback2 else rt_fault_callback);
}

fn rt_accessUnmappedMem(v_end: u32) void {
    use_callback2 = false;
    faulted = false;
    // Accessing unmapped mem causes a page fault
    var ptr = @intToPtr(*u8, v_end);
    var value = ptr.*;
    // This is the label that we return to after processing the page fault
    asm volatile (
        \\.global rt_fault_callback
        \\rt_fault_callback:
    );
    testing.expect(faulted);
    log.logInfo("Paging: Tested accessing unmapped memory\n", .{});
}

fn rt_accessMappedMem(v_end: u32) void {
    use_callback2 = true;
    faulted = false;
    // Accessing mapped memory does't cause a page fault
    var ptr = @intToPtr(*u8, v_end - PAGE_SIZE_4KB);
    var value = ptr.*;
    asm volatile (
        \\.global rt_fault_callback2
        \\rt_fault_callback2:
    );
    testing.expect(!faulted);
    log.logInfo("Paging: Tested accessing mapped memory\n", .{});
}

fn runtimeTests(v_end: u32) void {
    rt_accessUnmappedMem(v_end);
    rt_accessMappedMem(v_end);
}
