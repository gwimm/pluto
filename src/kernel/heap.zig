const std = @import("std");
const Allocator = std.mem.Allocator;

fn searchForBlockBelow(size: usize, start: usize, end: usize) ?ArrayList(HeapBlock) {
    var search_size = start;
    if (start == end)
        return null;
    // Search below and above if there aren't blocks of the search size
    return map.getValue(size) orelse searchForBlock(size, size,
}

pub fn alloc(size: usize) Allocator.Error!?usize {
    const midpoint = (largest - size) / 2 + size;
    var blocks: ?ArrayList(HeapBlock) = map.getValue(size) orelse searchForBlockBelow(size, size, midpoint) orelse searchForBlockAbove(size, midpoint, largest);
    if (blocks) |list| {
        const block = list.pop();
        if (list.size() == 0)
            map.remove(block.size);
        return block.addr;
    }
    return Allocator.Error.OutOfMemory;
}
