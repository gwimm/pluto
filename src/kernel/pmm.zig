const is_test = @import("builtin").is_test;
const std = @import("std");
const build_options = @import("build_options");
const mock_path = build_options.mock_path;
const arch = @import("arch.zig").internals;
const MemProfile = (if (is_test) @import(mock_path ++ "mem_mock.zig") else @import("mem.zig")).MemProfile;
const testing = std.testing;
const panic = @import("panic.zig").panic;
const log = @import("log.zig");
const MEMORY_AVAILABLE = @import("multiboot.zig").MULTIBOOT_MEMORY_AVAILABLE;
const Bitmap = @import("bitmap.zig").Bitmap;

const PmmBitmap = Bitmap(u32);

/// The possible errors thrown by bitmap functions
const PmmError = error{
    /// The address given hasn't been allocated
    NotAllocated,
};

/// The size of memory associated with each bitmap entry
const BLOCK_SIZE = arch.MEMORY_BLOCK_SIZE;

var bitmap: PmmBitmap = undefined;

///
/// Set the bitmap entry for an address as occupied
///
/// Arguments:
///     IN addr: usize - The address.
///
/// Error: PmmBitmap.BitmapError.
///     *: See PmmBitmap.setEntry. Could occur if the address is out of bounds.
///
fn setAddr(addr: usize) PmmBitmap.BitmapError!void {
    try bitmap.setEntry(@intCast(u32, addr / BLOCK_SIZE));
}

///
/// Check if an address is set as occupied.
///
/// Arguments:
///     IN addr: usize - The address to check.
///
/// Return: True if occupied, else false.
///
/// Error: PmmBitmap.BitmapError.
///     *: See PmmBitmap.setEntry. Could occur if the address is out of bounds.
///
fn isSet(addr: usize) PmmBitmap.BitmapError!bool {
    return bitmap.isSet(@intCast(u32, addr / BLOCK_SIZE));
}

///
/// Find the next free memory block, set it as occupied and return it. The region allocated will be of size BLOCK_SIZE.
///
/// Return: The address that was allocated.
///
pub fn alloc() ?usize {
    if (bitmap.setFirstFree()) |entry| {
        return entry * BLOCK_SIZE;
    }
    return null;
}

///
/// Set the address as free so it can be allocated in the future. This will free a block of size BLOCK_SIZE.
///
/// Arguments:
///     IN addr: usize - The previously allocated address to free. Will be aligned down to the nearest multiple of BLOCK_SIZE.
///
/// Error: PmmError || PmmBitmap.BitmapError.
///     PmmError.NotAllocated: The address wasn't allocated.
///     PmmBitmap.BitmapError.OutOfBounds: The address given was out of bounds.
///
pub fn free(addr: usize) (PmmBitmap.BitmapError || PmmError)!void {
    const idx = @intCast(u32, addr / BLOCK_SIZE);
    if (try bitmap.isSet(idx)) {
        try bitmap.clearEntry(idx);
    } else {
        return PmmError.NotAllocated;
    }
}

///
/// Intiialise the physical memory manager and set all unavailable regions as occupied (those from the memory map and those from the linker symbols).
///
/// Arguments:
///     IN mem: *const MemProfile - The system's memory profile.
///     IN allocator: *std.mem.Allocator - The allocator to use to allocate the bitmaps.
///
pub fn init(mem: *const MemProfile, allocator: *std.mem.Allocator) void {
    log.logInfo("Init pmm\n", .{});
    bitmap = PmmBitmap.init(mem.mem_kb * 1024 / BLOCK_SIZE, allocator) catch @panic("Bitmap allocation failed");

    // Occupy the regions of memory that the memory map describes as reserved
    for (mem.mem_map) |entry| {
        if (entry.@"type" != MEMORY_AVAILABLE) {
            var addr = std.mem.alignBackward(@intCast(usize, entry.addr), BLOCK_SIZE);
            var end = @intCast(usize, entry.addr + (entry.len - 1));
            // If the end address can be aligned without overflowing then align it
            if (end <= std.math.maxInt(usize) - BLOCK_SIZE)
                end = std.mem.alignForward(end, BLOCK_SIZE);
            while (addr < end) : (addr += BLOCK_SIZE) {
                setAddr(addr) catch |e| switch (e) {
                    // We can ignore out of bounds errors as the memory won't be available anyway
                    PmmBitmap.BitmapError.OutOfBounds => break,
                    else => panic(@errorReturnTrace(), "Failed setting address 0x{x} from memory map as occupied: {}", .{ addr, e }),
                };
            }
        }
    }
    // Occupy kernel memory
    var addr = std.mem.alignBackward(@ptrToInt(mem.physaddr_start), BLOCK_SIZE);
    while (addr < @ptrToInt(mem.physaddr_end)) : (addr += BLOCK_SIZE) {
        setAddr(addr) catch |e| switch (e) {
            error.OutOfBounds => panic(@errorReturnTrace(), "Failed setting kernel code address 0x{x} as occupied. The amount of system memory seems to be too low for the kernel image: {}", .{ addr, e }),
            else => panic(@errorReturnTrace(), "Failed setting kernel code address 0x{x} as occupied: {}", .{ addr, e }),
        };
    }
    log.logInfo("Done\n", .{});
    if (build_options.rt_test) {
        runtimeTests(mem);
    }
}

///
/// Allocate all blocks and make sure they don't overlap with any reserved addresses.
///
/// Arguments:
///     IN mem: *const MemProfile - The memory profile to check for reserved memory regions.
///
fn runtimeTests(mem: *const MemProfile) void {
    // Make sure that occupied memory can't be allocated
    var prev_alloc: usize = std.math.maxInt(usize);
    while (alloc()) |alloced| {
        if (prev_alloc == alloced) {
            panic(null, "PMM allocated the same address twice: 0x{x}", .{alloced});
        }
        prev_alloc = alloced;
        for (mem.mem_map) |entry| {
            if (entry.@"type" != MEMORY_AVAILABLE) {
                var addr = std.mem.alignBackward(@intCast(usize, entry.addr), BLOCK_SIZE);
                if (addr == alloced) {
                    panic(null, "PMM allocated an address that should be reserved by the memory map: 0x{x}", .{addr});
                }
            }
        }
        if (alloced >= std.mem.alignBackward(@ptrToInt(mem.physaddr_start), BLOCK_SIZE) and alloced < std.mem.alignForward(@ptrToInt(mem.physaddr_end), BLOCK_SIZE)) {
            panic(null, "PMM allocated an address that should be reserved by kernel code: 0x{x}", .{alloced});
        }
    }
    log.logInfo("PMM: Tested allocation\n", .{});
}

test "alloc" {
    bitmap = try Bitmap(u32).init(32, std.heap.direct_allocator);
    comptime var addr = 0;
    comptime var i = 0;
    // Allocate all entries, making sure they succeed and return the correct addresses
    inline while (i < 32) : ({
        i += 1;
        addr += BLOCK_SIZE;
    }) {
        testing.expect(!(try isSet(addr)));
        testing.expect(alloc().? == addr);
        testing.expect(try isSet(addr));
    }
    // Allocation should now fail
    testing.expect(alloc() == null);
}

test "free" {
    bitmap = try Bitmap(u32).init(32, std.heap.direct_allocator);
    comptime var i = 0;
    // Allocate and free all entries
    inline while (i < 32) : (i += 1) {
        const addr = alloc().?;
        testing.expect(try isSet(addr));
        try free(addr);
        testing.expect(!(try isSet(addr)));
        // Double frees should be caught
        testing.expectError(PmmError.NotAllocated, free(addr));
    }
}

test "setAddr and isSet" {
    const num_entries: u32 = 32;
    bitmap = try Bitmap(u32).init(num_entries, std.heap.direct_allocator);
    var addr: u32 = 0;
    var i: u32 = 0;
    while (i < num_entries) : ({
        i += 1;
        addr += BLOCK_SIZE;
    }) {
        // Ensure all previous blocks are still set
        var h: u32 = 0;
        var addr2: u32 = 0;
        while (h < i) : ({
            h += 1;
            addr2 += BLOCK_SIZE;
        }) {
            testing.expect(try isSet(addr2));
        }

        // Set the current block
        try setAddr(addr);
        testing.expect(try isSet(addr));

        // Ensure all successive entries are not set
        var j: u32 = i + 1;
        var addr3: u32 = addr + BLOCK_SIZE;
        while (j < num_entries) : ({
            j += 1;
            addr3 += BLOCK_SIZE;
        }) {
            testing.expect(!try isSet(addr3));
        }
    }
}
