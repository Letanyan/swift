//===--- BTreeNode.swift --------------------------------------*- swift -*-===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2018 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//

// `bTreeNodeSize` is the maximum size (in bytes) of the keys in a single,
// fully loaded B-tree node. This is related to the order of the B-tree, i.e.,
// the maximum number of children of an internal node.
//
// Common sense indicates (and benchmarking verifies) that the fastest B-tree
// order depends on `strideof(key)`: doubling the size of the key roughly halves
// the optimal order. So there is a certain optimal overall node size that
// is independent of the key; this value is supposed to be that size.
//
// Obviously, the optimal node size depends on the hardware we're running on.
// Benchmarks performed on various systems (Apple A5X, A8X, A9; Intel Core i5
// Sandy Bridge, Core i7 Ivy Bridge)
// indicate that 16KiB is a good overall choice.
// (This may be related to the size of the L1 cache, which is frequently 16kiB
// or 32kiB.)
//
// It is not a good idea to use powers of two as the B-tree order, as that would
// lead to Array reallocations just before
// a node is split. A node size that's just below 2^n seems like a good choice.
@usableFromInline
internal let bTreeNodeSize = 16383

// MARK: _BTreeNode definition

/// A node in an in-memory B-tree data structure, efficiently mapping
/// `Comparable` keys to arbitrary values.
/// Iterating over the elements in a B-tree returns them in ascending order of
/// their keys.
@usableFromInline
@_fixed_layout
internal final class _BTreeNode<Key: Equatable, Value> {
  @usableFromInline
  typealias Iterator = _BTreeIterator<Key, Value>
  @usableFromInline
  typealias Element = Iterator.Element
  @usableFromInline
  typealias Node = _BTreeNode<Key, Value>

  /// FIXME: Allocate keys/values/children in a single buffer

  /// The order which elements must follow
  @usableFromInline
  internal var areInIncreasingOrder: (Key, Key) -> Bool
  /// The elements stored in this node, sorted by are in increasing order.
  @usableFromInline
  internal var elements: [Element]
  /// An empty array (when this is a leaf), or `elements.count + 1` child nodes
  /// (when this is an internal node).
  @usableFromInline
  internal var children: [_BTreeNode]

  /// The number of elements in this B-tree.
  @usableFromInline
  internal var count: Int

  /// The order of this B-tree. An internal node will have at most this many
  /// children.
  @usableFromInline
  internal let _order: Int32
  /// The depth of this B-tree.
  @usableFromInline
  internal let _depth: Int32

  @inlinable
  internal var depth: Int { return numericCast(_depth) }
  @inlinable
  internal var order: Int { return numericCast(_order) }

  @inlinable
  internal init(
    order: Int,
    elements: [Element],
    children: [_BTreeNode],
    count: Int,
    areInIncreasingOrder: @escaping (Key, Key) -> Bool
  ) {
    assert(children.count == 0 || elements.count == children.count - 1)
    self._order = numericCast(order)
    self.elements = elements
    self.children = children
    self.count = count
    self._depth = (children.count == 0 ? 0 : children[0]._depth + 1)
    self.areInIncreasingOrder = areInIncreasingOrder
    let idx = children.firstIndex { $0._depth + (1 as Int32) != self._depth }
    assert(idx == nil)
  }
}

// MARK: Convenience initializers

extension _BTreeNode {
  @inlinable
  static var defaultOrder: Int {
    return Swift.max(bTreeNodeSize / MemoryLayout<Element>.stride, 8)
  }

  @inlinable
  internal convenience init(
    order: Int = Node.defaultOrder,
    areInIncreasingOrder: @escaping (Key, Key) -> Bool
  ) {
    self.init(
      order: order,
      elements: [],
      children: [],
      count: 0,
      areInIncreasingOrder: areInIncreasingOrder)
  }

  @inlinable
  internal convenience init(
    left: Node,
    separator: (key: Key, value: Value),
    right: Node,
    areInIncreasingOrder: @escaping (Key, Key) -> Bool
  ) {
    assert(left.order == right.order)
    assert(left.depth == right.depth)
    self.init(
      order: left.order,
      elements: [separator],
      children: [left, right],
      count: left.count + 1 + right.count,
      areInIncreasingOrder: areInIncreasingOrder)
  }

  @inlinable
  internal convenience init(
    node: _BTreeNode,
    slotRange: CountableRange<Int>
  ) {
    if node.isLeaf {
      let elements = Array(node.elements[slotRange])
      self.init(
        order: node.order,
        elements: elements,
        children: [],
        count: elements.count,
        areInIncreasingOrder: node.areInIncreasingOrder)
    } else if slotRange.count == 0 {
      let n = node.children[slotRange.lowerBound]
      self.init(
        order: n.order,
        elements: n.elements,
        children: n.children,
        count: n.count,
        areInIncreasingOrder: node.areInIncreasingOrder)
    } else {
      let elements = Array(node.elements[slotRange])
      let children = Array(
        node.children[slotRange.lowerBound ... slotRange.upperBound])
      let count = children.reduce(elements.count) { $0 + $1.count }
      self.init(
        order: node.order,
        elements: elements,
        children: children,
        count: count,
        areInIncreasingOrder: node.areInIncreasingOrder)
    }
  }
}

extension _BTreeNode where Key: Comparable {
  @inlinable
  internal convenience init(
    order: Int,
    elements: [Element],
    children: [_BTreeNode],
    count: Int
  ) {
    self.init(
      order: order, elements: elements, children: children, count: count,
      areInIncreasingOrder: <)
  }

  @inlinable
  internal convenience init(order: Int = Node.defaultOrder) {
    self.init(
      order: order,
      elements: [],
      children: [],
      count: 0,
      areInIncreasingOrder: <)
  }

  @inlinable
  internal convenience init(
    left: Node,
    separator: (key: Key, value: Value),
    right: Node
  ) {
    assert(left.order == right.order)
    assert(left.depth == right.depth)
    self.init(
      order: left.order,
      elements: [separator],
      children: [left, right],
      count: left.count + 1 + right.count,
      areInIncreasingOrder: <)
  }
}

// MARK: Uniqueness

extension _BTreeNode {
  @inlinable
  @discardableResult
  func makeChildUnique(_ index: Int) -> _BTreeNode {
    guard !isKnownUniquelyReferenced(&children[index]) else {
      return children[index]
    }
    let clone = children[index].clone()
    children[index] = clone
    return clone
  }

  @inlinable
  func clone() -> _BTreeNode {
    return _BTreeNode(
      order: order,
      elements: elements,
      children: children,
      count: count,
      areInIncreasingOrder: areInIncreasingOrder)
  }
}

// MARK: Basic limits and properties

extension _BTreeNode {
  @inlinable
  internal var maxChildren: Int { return order }
  @inlinable
  internal var minChildren: Int { return (maxChildren + 1) / 2 }
  @inlinable
  internal var maxKeys: Int { return maxChildren - 1 }
  @inlinable
  internal var minKeys: Int { return minChildren - 1 }

  @inlinable
  internal var isLeaf: Bool { return depth == 0 }
  @inlinable
  internal var isTooSmall: Bool { return elements.count < minKeys }
  @inlinable
  internal var isTooLarge: Bool { return elements.count > maxKeys }
  @inlinable
  internal var isBalanced: Bool {
    return elements.count >= minKeys && elements.count <= maxKeys
  }
}

extension _BTreeNode {
  @inlinable
  func lesserThan(_ a: Key, _ b: Key) -> Bool {
    return areInIncreasingOrder(a, b)
  }

  @inlinable
  func greaterThan(_ a: Key, _ b: Key) -> Bool {
    return !areInIncreasingOrder(a, b) && a != b
  }

  @inlinable
  func lesserThanOrEqual(_ a: Key, _ b: Key) -> Bool {
    return areInIncreasingOrder(a, b) || a == b
  }

  @inlinable
  func greaterThanOrEqual(_ a: Key, _ b: Key) -> Bool {
    return !areInIncreasingOrder(a, b)
  }
}

extension _BTreeNode: Sequence {
  @inlinable
  var isEmpty: Bool { return count == 0 }

  @inlinable
  func makeIterator() -> Iterator {
    return _BTreeIterator(_BTreeStrongPath(root: self, offset: 0))
  }

  /// Call `body` on each element in self in the same order as a for-in loop.
  @inlinable
  func forEach(_ body: (Element) throws -> Void) rethrows {
    if isLeaf {
      for element in elements {
        try body(element)
      }
    } else {
      for i in 0 ..< elements.count {
        try children[i].forEach(body)
        try body(elements[i])
      }
      try children[elements.count].forEach(body)
    }
  }

  /// A version of `forEach` that allows `body` to interrupt iteration by
  /// returning `false`.
  ///
  /// - Returns: `true` iff `body` returned true for all elements in the tree.
  @inlinable
  @discardableResult
  func forEach(_ body: (Element) throws -> Bool) rethrows -> Bool {
    if isLeaf {
      for element in elements {
        guard try body(element) else { return false }
      }
    } else {
      for i in 0 ..< elements.count {
        guard try children[i].forEach(body) else { return false }
        guard try body(elements[i]) else { return false }
      }
      guard try children[elements.count].forEach(body) else { return false }
    }
    return true
  }
}

extension _BTreeNode {
  @inlinable
  internal func setElement(inSlot slot: Int, to element: Element) -> Element {
    let old = elements[slot]
    elements[slot] = element
    return old
  }

  @inlinable
  internal func insert(_ element: Element, inSlot slot: Int) {
    elements.insert(element, at: slot)
    count += 1
  }

  @inlinable
  internal func append(_ element: Element) {
    elements.append(element)
    count += 1
  }

  @inlinable
  @discardableResult
  internal func remove(slot: Int) -> Element {
    count -= 1
    return elements.remove(at: slot)
  }

  /// Does one step toward looking up an element with `key`, returning the slot
  /// index of a direct match (if any),
  /// and the slot index to use to continue descending.
  ///
  /// - Complexity: O(log *m*), where *m* is `order`.
  @inline(__always)
  @inlinable
  internal func slot(
    of key: Key,
    choosing selector: _BTreeKeySelector = .first
  ) -> (match: Int?, descend: Int) {
    switch selector {
    case .first, .any:
      var start = 0
      var end = elements.count
      while start < end {
        let mid = start + (end - start) / 2
        if lesserThan(elements[mid].0, key) {
          start = mid + 1
        } else {
          end = mid
        }
      }
      return (start < elements.count
        && elements[start].0 == key ? start : nil, start)
    case .last:
      var start = -1
      var end = elements.count - 1
      while start < end {
        let mid = start + (end - start + 1) / 2
        if greaterThan(elements[mid].0, key) {
          end = mid - 1
        } else {
          start = mid
        }
      }
      return (start >= 0 && elements[start].0 == key ? start : nil, start + 1)
    case .after:
      var start = 0
      var end = elements.count
      while start < end {
        let mid = start + (end - start) / 2
        if lesserThanOrEqual(elements[mid].0, key) {
          start = mid + 1
        } else {
          end = mid
        }
      }
      return (start < elements.count ? start : nil, start)
    @unknown default:
      fatalError("unhandled unknown case")
    }
  }

  /// Return the slot of the element at `offset` in the subtree rooted at this
  /// node.
  @inlinable
  internal func slot(
    atOffset offset: Int
  ) -> (index: Int, match: Bool, offset: Int) {
    assert(offset >= 0 && offset <= count)
    if offset == count {
      return (index: elements.count, match: isLeaf, offset: count)
    }
    if isLeaf {
      return (offset, true, offset)
    } else if offset <= count / 2 {
      var p = 0
      for i in 0 ..< children.count - 1 {
        let c = children[i].count
        if offset == p + c {
          return (index: i, match: true, offset: p + c)
        }
        if offset < p + c {
          return (index: i, match: false, offset: p + c)
        }
        p += c + 1
      }
      let c = children.last!.count
      precondition(count == p + c, "Invalid B-Tree")
      return (index: children.count - 1, match: false, offset: count)
    }
    var p = count
    for i in (1 ..< children.count).reversed() {
      let c = children[i].count
      if offset == p - (c + 1) {
        return (index: i - 1, match: true, offset: offset)
      }
      if offset > p - (c + 1) {
        return (index: i, match: false, offset: p)
      }
      p -= c + 1
    }
    let c = children.first!.count
    precondition(p - c == 0, "Invalid B-Tree")
    return (index: 0, match: false, offset: c)
  }

  /// Return the offset of the element at `slot` in the subtree rooted at this
  /// node.
  @inlinable
  internal func offset(ofSlot slot: Int) -> Int {
    let c = elements.count
    assert(slot >= 0 && slot <= c)
    if isLeaf {
      return slot
    }
    if slot == c {
      return count
    }
    if slot <= c / 2 {
      return children[0...slot].reduce(slot) { $0 + $1.count }
    }
    return count - children[slot + 1 ... c].reduce(c - slot) { $0 + $1.count }
  }

  /// Returns true iff the subtree at this node is guaranteed to contain the
  /// specified element  with `key` (if it exists). Returns false if the key
  /// falls into the first or last child subtree, so containment depends on the
  /// contents of the ancestors of this node.
  @inlinable
  internal func contains(
    _ key: Key,
    choosing selector: _BTreeKeySelector
  ) -> Bool {
    let firstKey = elements.first!.0
    let lastKey = elements.last!.0
    if lesserThan(key, firstKey) {
      return false
    }
    if key == firstKey && selector == .first {
      return false
    }
    if greaterThan(key, lastKey) {
      return false
    }
    if key == lastKey && (selector == .last || selector == .after) {
      return false
    }
    return true
  }
}

// MARK: Lookups

extension _BTreeNode {
  /// Returns the first element at or under this node, or `nil` if this node is
  /// empty.
  ///
  /// - Complexity: O(log *n*), where *n* is the length of the node.
  @inlinable
  var first: Element? {
    var node = self
    while let child = node.children.first {
      node = child
    }
    return node.elements.first
  }

  /// Returns the last element at or under this node, or `nil` if this node is
  /// empty.
  ///
  /// - Complexity: O(log *n*), where *n* is the length of the node.
  @inlinable
  var last: Element? {
    var node = self
    while let child = node.children.last {
      node = child
    }
    return node.elements.last
  }
}

// MARK: Splitting
@usableFromInline
@_fixed_layout
internal struct _BTreeSplinter<Key: Equatable, Value> {
  @usableFromInline
  var separator: (key: Key, value: Value)
  @usableFromInline
  var node: _BTreeNode<Key, Value>

  @inlinable
  init(separator: (key: Key, value: Value), node: _BTreeNode<Key, Value>) {
    self.separator = separator
    self.node = node
  }
}

extension _BTreeNode {
  @usableFromInline
  typealias Splinter = _BTreeSplinter<Key, Value>

  /// Split this node into two, removing the high half of the nodes and putting
  /// them in a splinter.
  ///
  /// - Returns: A splinter containing the higher half of the original node.
  @inlinable
  internal func split() -> Splinter {
    assert(isTooLarge)
    return split(at: elements.count / 2)
  }

  /// Split this node into two at the key at index `median`, removing all
  /// elements at or above `median` and putting them in a splinter.
  ///
  /// - Returns: A splinter containing the higher half of the original node.
  @inlinable
  internal func split(at median: Int) -> Splinter {
    let count = elements.count
    let separator = elements[median]
    let node = _BTreeNode(node: self, slotRange: median + 1 ..< count)
    elements.removeSubrange(median ..< count)
    if isLeaf {
      self.count = median
    } else {
      children.removeSubrange(median + 1 ..< count + 1)
      self.count = median + children.reduce(0, { $0 + $1.count })
    }
    assert(node.depth == self.depth)
    return Splinter(separator: separator, node: node)
  }

  @inlinable
  internal func insert(_ splinter: Splinter, inSlot slot: Int) {
    elements.insert(splinter.separator, at: slot)
    children.insert(splinter.node, at: slot + 1)
  }
}

// MARK: Removal

extension _BTreeNode {
  /// Reorganize the tree rooted at `self` so that the undersize child in `slot`
  /// is corrected. As a side effect of the process, `self` may itself become
  /// undersized, but all of its descendants become balanced.
  @inlinable
  internal func fixDeficiency(_ slot: Int) {
    assert(!isLeaf && children[slot].isTooSmall)
    if slot > 0 && children[slot - 1].elements.count > minKeys {
      rotateRight(slot)
    } else if slot < children.count - 1
      && children[slot + 1].elements.count > minKeys {
      rotateLeft(slot)
    } else if slot > 0 {
      // Collapse deficient slot into previous slot.
      collapse(slot - 1)
    } else {
      // Collapse next slot into deficient slot.
      collapse(slot)
    }
  }

  @inlinable
  internal func rotateRight(_ slot: Int) {
    assert(slot > 0)
    makeChildUnique(slot)
    makeChildUnique(slot - 1)
    children[slot].elements.insert(elements[slot - 1], at: 0)
    if !children[slot].isLeaf {
      let lastGrandChildBeforeSlot = children[slot - 1].children.removeLast()
      children[slot].children.insert(lastGrandChildBeforeSlot, at: 0)

      children[slot - 1].count -= lastGrandChildBeforeSlot.count
      children[slot].count += lastGrandChildBeforeSlot.count
    }
    elements[slot - 1] = children[slot - 1].elements.removeLast()
    children[slot - 1].count -= 1
    children[slot].count += 1
  }

  @inlinable
  internal func rotateLeft(_ slot: Int) {
    assert(slot < children.count - 1)
    makeChildUnique(slot)
    makeChildUnique(slot + 1)
    children[slot].elements.append(elements[slot])
    if !children[slot].isLeaf {
      let firstGrandChildAfterSlot = children[slot + 1].children.remove(at: 0)
      children[slot].children.append(firstGrandChildAfterSlot)

      children[slot + 1].count -= firstGrandChildAfterSlot.count
      children[slot].count += firstGrandChildAfterSlot.count
    }
    elements[slot] = children[slot + 1].elements.remove(at: 0)
    children[slot].count += 1
    children[slot + 1].count -= 1
  }

  @inlinable
  internal func collapse(_ slot: Int) {
    assert(slot < children.count - 1)
    makeChildUnique(slot)
    let next = children.remove(at: slot + 1)
    children[slot].elements.append(elements.remove(at: slot))
    children[slot].count += 1
    children[slot].elements.append(contentsOf: next.elements)
    children[slot].count += next.count
    if !next.isLeaf {
      children[slot].children.append(contentsOf: next.children)
    }
    assert(children[slot].isBalanced)
  }
}

// MARK: Join

extension _BTreeNode {
  /// Shift slots between `self` and `node` such that the number of elements in
  /// `self` becomes `target`.
  @inlinable
  internal func shiftSlots(
    separator: Element,
    node: _BTreeNode,
    target: Int
  ) -> Splinter? {
    assert(self.depth == node.depth)

    let forward = target > self.elements.count
    let delta = abs(target - self.elements.count)
    if delta == 0 {
      return Splinter(separator: separator, node: node)
    }
    let lc = self.elements.count
    let rc = node.elements.count

    if (forward && delta >= rc + 1) || (!forward && delta >= lc + 1) {
      // Melt the entire right node into self.
      self.elements.append(separator)
      self.elements.append(contentsOf: node.elements)
      self.children.append(contentsOf: node.children)
      node.elements = []
      node.children = []
      self.count += 1 + node.count
      return nil
    }

    let rsep: Element
    if forward { // Transfer slots from right to left
      assert(lc + delta < self.order)
      assert(delta <= rc)

      rsep = node.elements[delta - 1]

      self.elements.append(separator)
      self.elements.append(contentsOf: node.elements.prefix(delta - 1))
      self.count += delta

      node.elements.removeFirst(delta)
      node.count -= delta

      if !self.isLeaf {
        let children = node.children.prefix(delta)
        let dc = children.reduce(0) { $0 + $1.count }
        self.children.append(contentsOf: children)
        self.count += dc

        node.children.removeFirst(delta)
        node.count -= dc
      }
    } else {
      // Transfer slots from left to right
      assert(rc + delta < node.order)
      assert(delta <= lc)

      rsep = self.elements[lc - delta]

      node.elements.insert(separator, at: 0)
      node.elements.insert(contentsOf: self.elements.suffix(delta - 1), at: 0)
      node.count += delta

      self.elements.removeSubrange(lc - delta ..< lc)
      self.count -= delta

      if !self.isLeaf {
        let children = self.children.suffix(delta)
        let dc = children.reduce(0) { $0 + $1.count }
        node.children.insert(contentsOf: children, at: 0)
        node.count += dc

        self.children.removeSubrange(lc + 1 - delta ..< lc + 1)
        self.count -= dc
      }
    }
    if node.children.count == 1 {
      return Splinter(separator: rsep, node: node.makeChildUnique(0))
    }
    return Splinter(separator: rsep, node: node)
  }

  @inlinable
  func swapContents(with other: Node) {
    precondition(self._depth == other._depth)
    precondition(self._order == other._order)
    swap(&self.elements, &other.elements)
    swap(&self.children, &other.children)
    swap(&self.count, &other.count)
  }

  /// Create and return a new B-tree consisting of elements of `left`,
  /// `separator` and the elements of `right`, in this order.
  ///
  /// If you need to keep `left` and `right` intact, clone them before calling
  /// this function.
  ///
  /// - Requires: `l <= separator.0 && separator.0 <= r` for all keys `l` in
  ///   `left` and all keys `r` in `right`.
  /// - Complexity: O(log(*n* + *m*)), where *n* is the length of
  ///   the left node and *m* is the length of the right node.
  @inlinable
  internal static func join(
    left: _BTreeNode,
    separator: (key: Key, value: Value),
    right: _BTreeNode,
    areInIncreasingOrder: @escaping (Key, Key) -> Bool
  ) -> _BTreeNode {
    precondition(left.order == right.order)

    let order = left.order
    let depthDelta = left.depth - right.depth
    let append = depthDelta >= 0

    let stock = append ? left : right
    let scion = append ? right : left
    // We'll graft the scion onto the stock.

    // First, find the insertion point, and preemptively update node counts on
    // the way there.
    var path = [stock]
    var node = stock
    let c = scion.count
    for _ in 0 ..< abs(depthDelta) {
      node.count += c + 1
      node = node.makeChildUnique(append ? node.children.count - 1 : 0)
      path.append(node)
    }

    // Graft the scion into the stock by inserting the contents of its root into
    // `node`.
    if !append { node.swapContents(with: scion) }
    assert(node.depth == scion.depth)
    let slotCount = node.elements.count + 1 + scion.elements.count
    let target = slotCount < order ? slotCount : slotCount / 2
    var splinter = node.shiftSlots(
      separator: separator, node: scion, target: target)
    if splinter != nil {
      assert(splinter!.node.isBalanced)
      path.removeLast()
      while let s = splinter, !path.isEmpty {
        let node = path.removeLast()
        node.insert(s, inSlot: append ? node.elements.count : 0)
        splinter = node.isTooLarge ? node.split() : nil
      }
      if let s = splinter {
        return _BTreeNode(
          left: stock, separator: s.separator, right: s.node,
          areInIncreasingOrder: areInIncreasingOrder)
      }
    }
    return stock
  }
}

extension _BTreeNode where Key: Comparable {
  @inlinable
  internal static func join(
    left: _BTreeNode,
    separator: (key: Key, value: Value),
    right: _BTreeNode
  ) -> _BTreeNode {
    return _BTreeNode.join(
      left: left, separator: separator, right: right, areInIncreasingOrder: <)
  }
}
