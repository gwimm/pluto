const std = @import("std");
const Allocator = std.mem.Allocator;

// size(tree) = 2^height(t) - 1
// height(tree) = block_max_size(tree) >> log2(block_min_size(tree))
const BuddyTree = struct {
    left: ?*BuddyTree,
    right: ?*BuddyTree,
    parent: ?*BuddyTree,
    allocated: bool,
    free_descendants: bool,

    fn isAllocatable(self: *BuddyTree) bool {
        return !self.allocated and self.free_descendants;
    }

    fn search(self: *BuddyTree, size: usize, block_size: usize, min_block_size: usize, addr: usize, end_addr: usize, res_addr: *usize, allocator: *std.mem.Allocator) std.mem.Allocator.Error!?*BuddyTree {
        // If we reach the end of the allocatable space, fail
        if (addr >= end_addr)
            return null;
        // If both the block and its children are free then this block can be allocated
        if (block_size == size) {
            if (self.isAllocatable()) {
                res_addr.* = addr;
                return self;
            }
            return null;
        }
        // If the all blocks greater than or equal to the desired size are allocated then fail
        if (block_size < size)
            return null;

        // If this block's children are not free then fail
        if (self.allocated or !self.free_descendants)
            return null;

        // The size of this block's children is this block's size divided by two
        const child_size = block_size / 2;
        // There are no smaller blocks so fail
        if (child_size < min_block_size)
            return null;
        // If the left child doesn't exist then create and search it. This will succeed as it and its potential children haven't been allocated yet
        if (self.left == null) {
            var left = try allocator.create(BuddyTree);
            left.left = null;
            left.right = null;
            left.parent = self;
            left.allocated = false;
            left.free_descendants = true;
            self.left = left;
            return search(left, size, child_size, min_block_size, addr, end_addr, res_addr, allocator);
        }
        // If the right child doesn't exist then create it and search it. This will succeed as it and its potential children haven't been allocated yet
        if (self.right == null) {
            var right = try allocator.create(BuddyTree);
            right.left = null;
            right.right = null;
            right.parent = self;
            right.allocated = false;
            right.free_descendants = true;
            self.right = right;
            return search(right, size, child_size, min_block_size, addr + child_size, end_addr, res_addr, allocator);
        }

        // If both children exist, then search the left one and return its result if it found one.
        // The unreachable here is fine since we checked for it being null above
        if (try search(self.left orelse unreachable, size, child_size, min_block_size, addr, end_addr, res_addr, allocator)) |t|
            return t;
        // Otherwise the right child is our last chance
        // The unreachable here is fine since we checked for it being null above
        return try search(self.right orelse unreachable, size, child_size, min_block_size, addr + child_size, end_addr, res_addr, allocator);
    }

    pub fn deinit(self: *@This(), allocator: *std.mem.Allocator) void {
        if (self.left) |l|
            l.deinit(allocator);
        if (self.right) |r|
            r.deinit(allocator);
        allocator.destroy(self);
    }
};

const Error = error{NonPowerOfTwo};

const BuddyAllocator = struct {
    root: *BuddyTree,
    block_min_size: usize,
    block_max_size: usize,
    start: usize,
    end: usize,

    pub fn init(start: usize, end: usize, block_min_size: usize, block_max_size: usize, allocator: *std.mem.Allocator) (std.mem.Allocator.Error || Error)!BuddyAllocator {
        if (@popCount(block_max_size) != 1)
            return Error.NonPowerOfTwo;
        return BuddyAllocator{
            .root = try allocator.init(BuddyTree),
            .block_min_size = block_min_size,
            .block_max_size = block_max_size,
            .start = start,
            .end = end,
        };
    }

    pub fn alloc(self: *Self, size: usize, alignment: u31) ?usize {
        // Find the next power of 2 greater than or equal to the desired size, but not larger than the minimum block size
        const pow2_size = std.math.max(std.math.pow(usize, 2, @ceil(std.math.log2(size))), self.min_block_size);

        if (pow2_size > self.block_max_size)
            return OutOfMemory;

        var addr = self.start;
        var block_size = self.block_max_size;
        var tree = self.root.search(pow2_size, block_size, self.block_min_size, &addr);
        if (tree) |*t| {
            t.free = false;
            // Tell all ancestors that one of their descendants is no longer free
            var parent = t.parent orelse unreachable;
            while (parent) |p| {
                // If this ancestor already knows a descendant is no longer free or is allocated itself, we don't need to continue
                if (!parent.free_descendants or parent.allocated)
                    break;
                p.free_descendants = false;
                parent = p.parent;
            }
            return addr;
        }
        return null;
    }
};

test "search" {
    var tree = BuddyTree{ .right = null, .left = null, .parent = null, .allocated = false, .free_descendants = true };
    var original = tree;
    const block_min: u32 = 4;
    const block_max: u32 = 16;
    var addr: usize = 0;
    var size: usize = block_max;

    // Searching for a block of the same size as the root (which is free) should return the root with no children created
    var res = (try tree.search(size, block_max, block_min, 0, 0xFFFFF, &addr, std.testing.allocator)).?;
    std.testing.expectEqual(res, &tree);
    std.testing.expectEqual(addr, 0);
    std.testing.expectEqual(res.*, original);
    std.testing.expect(res.free_descendants);
    std.testing.expect(!res.allocated);
    res.allocated = true;
    original.allocated = true;

    // Trying to allocate any size should now fail
    while (size > 0) : (size /= 2) {
        const a = addr;
        const res2 = try tree.search(size, block_max, block_min, 0, 0xFFFFF, &addr, std.testing.allocator);
        std.testing.expectEqual(res2, null);
        std.testing.expectEqual(tree, original);
        std.testing.expectEqual(addr, a);
    }

    // Deallocate the root and test searching for smaller blocks
    res.allocated = false;
    original.allocated = false;

    // Search for a block of size max/2
    // This should create and return the left child of the root
    res = (try tree.search(block_max / 2, block_max, block_min, 0, 0xFFFF, &addr, std.testing.allocator)).?;
    var left = BuddyTree{ .left = null, .right = null, .allocated = false, .free_descendants = true, .parent = &tree };
    std.testing.expect(tree.left != null);
    std.testing.expectEqual(tree.left.?.*, left);
    std.testing.expectEqual(res, tree.left.?);
    std.testing.expectEqual(tree.right, null);
    tree.left.?.allocated = true;
    left.allocated = true;

    // Search for a block of size max/4
    // This should create two layers on the root's right child
    res = (try tree.search(block_max / 4, block_max, block_min, 0, 0xFFFF, &addr, std.testing.allocator)).?;
    var right_left = BuddyTree{ .left = null, .right = null, .parent = tree.right, .allocated = false, .free_descendants = true };
    std.testing.expect(tree.right != null);
    std.testing.expect(tree.right.?.left != null);
    std.testing.expectEqual(tree.right.?.left.?.*, right_left);
    std.testing.expectEqual(res, tree.right.?.left.?);
    // The left child shouldn't have been modified
    std.testing.expect(tree.left != null);
    std.testing.expectEqual(tree.left.?.*, left);
    tree.right.?.left.?.allocated = true;
    right_left.allocated = true;

    // Now try searching for the last remaining block, which is of size max/4 and is the right child of the root's right child
    res = (try tree.search(block_max / 4, block_max, block_min, 0, 0xFFFF, &addr, std.testing.allocator)).?;
    // Make sure the right child of the root's right child was set
    var right_right: BuddyTree = .{ .left = null, .right = null, .allocated = false, .free_descendants = true, .parent = tree.right.? };
    std.testing.expect(tree.right != null);
    std.testing.expect(tree.right.?.right != null);
    std.testing.expectEqual(tree.right.?.right.?.*, right_right);
    std.testing.expectEqual(res, tree.right.?.right.?);
    // The left child of the root's right child shouldn't have changed
    std.testing.expect(tree.right.?.left != null);
    std.testing.expectEqual(tree.right.?.left.?.*, right_left);
    // The left child shouldn't have been modified
    std.testing.expect(tree.left != null);
    std.testing.expectEqual(tree.left.?.*, left);
    tree.right.?.right.?.allocated = true;
    right_right.allocated = true;

    original = tree;
    // Try searching for more blocks, all of which should fail, leaving the tree unchanged
    size = block_max / 8;
    while (size <= block_max) : (size *= 2) {
        std.testing.expectEqual(try tree.search(block_min / 2, block_max, block_min, 0, 0xFFFF, &addr, std.testing.allocator), null);
        std.testing.expectEqual(tree, original);
    }

    // Clean up
    if (tree.left) |l|
        l.deinit(std.testing.allocator);
    if (tree.right) |r|
        r.deinit(std.testing.allocator);
}
