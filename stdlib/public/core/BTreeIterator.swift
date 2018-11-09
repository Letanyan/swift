//===--- BTreeIterator.swift ----------------------------------*- swift -*-===//
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

/// An iterator for all elements stored in a B-tree, in ascending key order.
@usableFromInline
@_fixed_layout
internal struct _BTreeIterator<Key: Comparable, Value>: IteratorProtocol {
  @usableFromInline
  internal typealias Element = (key: Key, value: Value)
  @usableFromInline
  typealias Node = _BTreeNode<Key, Value>
  @usableFromInline
  typealias State = _BTreeStrongPath<Key, Value>

  @usableFromInline
  var state: State

  @inlinable
  internal init(_ state: State) {
    self.state = state
  }

  /// Advance to the next element and return it, or return `nil` if no next
  /// element exists.
  ///
  /// - Complexity: Amortized O(1)
  @inlinable
  internal mutating func next() -> Element? {
    if state.isAtEnd { return nil }
    let result = state.element
    state.moveForward()
    return result
  }
}

/// A dummy, zero-size key that is useful in B-trees that don't need key-based
/// lookup.
@usableFromInline
@_fixed_layout
internal struct EmptyKey: Comparable {
  @inlinable
  internal static func == (a: EmptyKey, b: EmptyKey) -> Bool { return true }
  @inlinable
  internal static func < (a: EmptyKey, b: EmptyKey) -> Bool { return false }
}

/// An iterator for the values stored in a B-tree with an empty key.
@usableFromInline
@_fixed_layout
internal struct _BTreeValueIterator<Value>: IteratorProtocol {
  @usableFromInline
  internal typealias Base = _BTreeIterator<EmptyKey, Value>
  @usableFromInline
  internal var base: Base

  @inlinable
  internal init(_ base: Base) {
    self.base = base
  }

  /// Advance to the next element and return it, or return `nil` if no next
  /// element exists.
  ///
  /// - Complexity: Amortized O(1)
  @inlinable
  internal mutating func next() -> Value? {
    return base.next()?.1
  }
}

/// An iterator for the keys stored in a B-tree without a value.
@usableFromInline
@_fixed_layout
internal struct _BTreeKeyIterator<Key: Comparable>: IteratorProtocol {
  @usableFromInline
  internal typealias Base = _BTreeIterator<Key, Void>
  @usableFromInline
  internal var base: Base

  @inlinable
  internal init(_ base: Base) {
    self.base = base
  }

  /// Advance to the next element and return it, or return `nil` if no next
  /// element exists.
  ///
  /// - Complexity: Amortized O(1)
  @inlinable
  internal mutating func next() -> Key? {
    return base.next()?.0
  }
}

/// A protocol that represents a mutable path from the root of a B-tree to one
/// of its elements. The extension methods defined on `_BTreePath` provide a
/// uniform way to navigate around in a B-tree, independent of the details of
/// the path representation.
///
/// There are three concrete implementations of this protocol:
///
/// - `_BTreeStrongPath` holds strong references and doesn't support modifying
///    the tree. It is used by `_BTreeIterator`.
/// - `_BTreeWeakPath` holds weak references and doesn't support modifying the
///    tree. It is used by `_BTreeIndex`.
/// - `_BTreeCursorPath` holds strong references and supports modifying the tree.
///    It is used by `_BTreeCursor`.
///
/// This protocol saves us from having to maintain three slightly different
/// variants of the same navigation methods.
@usableFromInline
internal protocol _BTreePath {
  associatedtype Key: Comparable
  associatedtype Value

  /// Create a new incomplete path focusing at the root of a tree.
  init(root: _BTreeNode<Key, Value>)

  /// The root node of the underlying B-tree.
  var root: _BTreeNode<Key, Value> { get }

  /// The current offset of this path. (This is a simple stored property. Use
  /// `move(to:)` to reposition
  /// the path on a different offset.)
  var offset: Int { get set }

  /// The number of elements in the tree.
  var count: Int { get }

  /// The number of nodes on the path from the root to the node that holds the
  /// focused element, including both ends.
  var length: Int { get }

  /// The final node on the path; i.e., the node that holds the currently
  /// focused element.
  var node: _BTreeNode<Key, Value> { get }

  /// The final slot on the path, or `nil` if the path is currently incomplete.
  var slot: Int? { get set }

  /// Pop the last slot in `slots`, creating an incomplete path.
  /// The path's `offset` is updated to the offset of the element following the
  /// subtree at the last node.
  mutating func popFromSlots()

  /// Pop the last node in an incomplete path, focusing the element following
  /// its subtree. This restores the path to a completed state.
  mutating func popFromPath()

  /// Push the child node before the currently focused element on the path,
  /// creating an incomplete path.
  mutating func pushToPath()

  /// Push the specified slot onto `slots`, completing the path.
  /// The path's `offset` is updated to the offset of the currently focused
  /// element.
  mutating func pushToSlots(_ slot: Int, offsetOfSlot: Int)

  /// Call `body` for each node and associated slot on the current path.
  /// If `ascending` is `true`, the calls proceed upwards, from the deepest node
  /// to the root; otherwise nodes are listed starting with the root down to the
  /// final path element.
  func forEach(ascending: Bool, body: (_BTreeNode<Key, Value>, Int) -> Void)

  /// Call `body` for each slot index on the way from the currently selected
  /// element up to the root node. If `ascending` is `true`, the calls proceed
  /// upwards, from the slot of deepest node to the root; otherwise slots are
  /// listed starting with the slot of the root down to the final path element.
  ///
  /// This method must not look at the nodes on the path (if this path uses
  /// weak/unowned references, they may have been invalidated).
  func forEachSlot(ascending: Bool, body: (Int) -> Void)

  /// Finish working with the path and return the root node.
  mutating func finish() -> _BTreeNode<Key, Value>
}

extension _BTreePath {
  @usableFromInline
  internal typealias Element = (key: Key, value: Value)
  @usableFromInline
  internal typealias Tree = _BTree<Key, Value>
  @usableFromInline
  internal typealias Node = _BTreeNode<Key, Value>

  @inlinable
  init(startOf root: Node) {
    self.init(root: root, offset: 0)
  }

  @inlinable
  init(endOf root: Node) {
    // The end offset can be anywhere on the rightmost path of the tree,
    // so let's try the spot after the last element of the root.
    // This can spare us O(log *n*) steps if this path is only used for
    // reference.
    self.init(root: root)
    pushToSlots(root.elements.count, offsetOfSlot: root.count)
  }

  @inlinable
  init(root: Node, offset: Int) {
    self.init(root: root)
    descend(toOffset: offset)
  }

  @inlinable
  init(root: Node, key: Key, choosing selector: _BTreeKeySelector) {
    self.init(root: root)
    descend(to: key, choosing: selector)
  }

  @inlinable
  init<Path: _BTreePath>(root: Node, slotsFrom path: Path)
    where Path.Key == Key, Path.Value == Value {
      self.init(root: root)
      path.forEachSlot(ascending: false) { slot in
        if self.slot != nil {
          pushToPath()
        }
        self.pushToSlots(slot)
      }
  }

  /// Return true iff the path contains at least one node.
  @inlinable
  var isValid: Bool { return length > 0 }
  /// Return true iff the current position is at the start of the tree.
  @inlinable
  var isAtStart: Bool { return offset == 0 }
  /// Return true iff the current position is at the end of the tree.
  @inlinable
  var isAtEnd: Bool { return offset == count }

  /// Push the specified slot onto `slots`, completing the path.
  @inlinable
  mutating func pushToSlots(_ slot: Int) {
    pushToSlots(slot, offsetOfSlot: node.offset(ofSlot: slot))
  }

  @inlinable
  mutating func finish() -> Node {
    return root
  }

  /// Return the element at the current position.
  @inlinable
  var element: Element { return node.elements[slot!] }
  /// Return the key of the element at the current position.
  @inlinable
  var key: Key { return element.0 }
  /// Return the value of the element at the current position.
  @inlinable
  var value: Value { return element.1 }

  /// Move to the next element in the B-tree.
  ///
  /// - Requires: `!isAtEnd`
  /// - Complexity: Amortized O(1)
  @inlinable
  mutating func moveForward() {
    precondition(offset < count)
    offset += 1
    if node.isLeaf {
      if slot! < node.elements.count - 1 || offset == count {
        slot! += 1
      } else {
        // Ascend
        repeat {
          slot = nil
          popFromPath()
        } while slot == node.elements.count
      }
    } else {
      // Descend
      slot! += 1
      pushToPath()
      while !node.isLeaf {
        slot = 0
        pushToPath()
      }
      slot = 0
    }
  }

  /// Move to the previous element in the B-tree.
  ///
  /// - Requires: `!isAtStart`
  /// - Complexity: Amortized O(1)
  @inlinable
  mutating func moveBackward() {
    precondition(!isAtStart)
    offset -= 1
    if node.isLeaf {
      if slot! > 0 {
        slot! -= 1
      } else {
        // Ascend
        repeat {
          slot = nil
          popFromPath()
        } while slot! == 0
        slot! -= 1
      }
    } else {
      // Descend
      assert(!node.isLeaf)
      pushToPath()
      while !node.isLeaf {
        slot = node.children.count - 1
        pushToPath()
      }
      slot = node.elements.count - 1
    }
  }

  /// Move to the start of the B-tree.
  ///
  /// - Complexity: O(log *n*), where *n* is `offset`
  @inlinable
  mutating func moveToStart() {
    move(toOffset: 0)
  }

  /// Move to the end of the B-tree.
  ///
  /// - Complexity: O(log(*n* - *m*)), where *n* is is the length of the
  ///   collection and *m* is `offset`
  @inlinable
  mutating func moveToEnd() {
    popFromSlots()
    while self.count > self.offset {
      popFromPath()
      popFromSlots()
    }
    self.descend(toOffset: self.count)
  }

  /// Move to the specified offset in the B-tree.
  ///
  /// - Complexity: O(log *n*), where *n* is the absolute
  ///   difference between the desired and current offsets.
  @inlinable
  mutating func move(toOffset offset: Int) {
    precondition(offset >= 0 && offset <= count)
    if offset == count {
      moveToEnd()
      return
    }
    // Pop to ancestor whose subtree contains the desired offset.
    popFromSlots()
    while offset < self.offset - node.count || offset >= self.offset {
      popFromPath()
      popFromSlots()
    }
    self.descend(toOffset: offset)
  }

  /// Move to the element with the specified key.
  /// If there are no such elements, move to the first element after `key` (or
  /// at the end of tree). If there are multiple such elements, `selector`
  /// determines which one to find.
  ///
  /// - Complexity: O(log *n*), where *n* is is the length of the collection
  @inlinable
  mutating func move(to key: Key, choosing selector: _BTreeKeySelector = .any) {
    popFromSlots()
    while length > 1 && !node.contains(key, choosing: selector) {
      popFromPath()
      popFromSlots()
    }
    self.descend(to: key, choosing: selector)
  }

  /// Starting from an incomplete path, descend to the element at the specified
  /// offset.
  @inlinable
  mutating func descend(toOffset offset: Int) {
    assert(offset >= self.offset - node.count && offset <= self.offset)
    assert(self.slot == nil)
    var slot = node.slot(atOffset: offset - (self.offset - node.count))
    pushToSlots(slot.index, offsetOfSlot: slot.offset)
    while !slot.match {
      pushToPath()
      slot = node.slot(atOffset: offset - (self.offset - node.count))
      pushToSlots(slot.index, offsetOfSlot: slot.offset)
    }
    assert(self.offset == offset)
    assert(self.slot != nil)
  }

  /// Starting from an incomplete path, descend to the element with the
  /// specified key.
  @inlinable
  mutating func descend(to key: Key, choosing selector: _BTreeKeySelector) {
    assert(self.slot == nil)
    if count == 0 {
      pushToSlots(0)
      return
    }

    var match: (depth: Int, slot: Int)? = nil
    while true {
      let slot = node.slot(of: key, choosing: selector)
      if let m = slot.match {
        if node.isLeaf || selector == .any {
          pushToSlots(m)
          return
        }
        match = (depth: length, slot: m)
      }
      if node.isLeaf {
        if let m = match {
          for _ in 0 ..< length - m.depth {
            popFromPath()
            popFromSlots()
          }
          pushToSlots(m.slot)
        } else if slot.descend < node.elements.count {
          pushToSlots(slot.descend)
        } else {
          pushToSlots(slot.descend - 1)
          moveForward()
        }
        break
      }
      pushToSlots(slot.descend)
      pushToPath()
    }
  }

  /// Return a tuple containing a tree with all elements before the current
  /// position, the currently focused element, and a tree with all elements
  /// after the currrent position.
  ///
  /// - Complexity: O(log *n*), where *n* is the length of the collection
  @inlinable
  func split() -> (prefix: Tree, separator: Element, suffix: Tree) {
    precondition(!isAtEnd)
    var left: Node? = nil
    var separator: Element? = nil
    var right: Node? = nil
    forEach(ascending: true) { node, slot in
      if separator == nil {
        left = Node(node: node, slotRange: 0 ..< slot)
        separator = node.elements[slot]
        let c = node.elements.count
        right = Node(node: node, slotRange: slot + 1 ..< c)
      } else {
        if slot >= 1 {
          let l = Node(node: node, slotRange: 0 ..< slot - 1)
          let s = node.elements[slot - 1]
          left = Node.join(left: l, separator: s, right: left!)
        }
        let c = node.elements.count
        if slot <= c - 1 {
          let r = Node(node: node, slotRange: slot + 1 ..< c)
          let s = node.elements[slot]
          right = Node.join(left: right!, separator: s, right: r)
        }
      }
    }
    return (Tree(left!), separator!, Tree(right!))
  }

  /// Return a tree containing all elements before (and not including) the
  /// current position.
  ///
  /// - Complexity: O(log *n*), where *n* is the length of the collection
  @inlinable
  func prefix() -> Tree {
    precondition(!isAtEnd)
    var prefix: Node? = nil
    forEach(ascending: true) { node, slot in
      if prefix == nil {
        prefix = Node(node: node, slotRange: 0 ..< slot)
      } else if slot >= 1 {
        let l = Node(node: node, slotRange: 0 ..< slot - 1)
        let s = node.elements[slot - 1]
        prefix = Node.join(left: l, separator: s, right: prefix!)
      }
    }
    return Tree(prefix!)
  }

  /// Return a tree containing all elements after (and not including) the
  /// current position.
  ///
  /// - Complexity: O(log *n*), where *n* is the length of the collection
  @inlinable
  func suffix() -> Tree {
    precondition(!isAtEnd)
    var suffix: Node? = nil
    forEach(ascending: true) { node, slot in
      if suffix == nil {
        let c = node.elements.count
        suffix = Node(node: node, slotRange: slot + 1 ..< c)
        return
      }
      let c = node.elements.count
      if slot <= c - 1 {
        let r = Node(node: node, slotRange: slot + 1 ..< c)
        let s = node.elements[slot]
        suffix = Node.join(left: suffix!, separator: s, right: r)
      }
    }
    return Tree(suffix!)
  }
}

/// A mutable path in a B-tree, holding weak references to nodes on the path.
/// This path variant does not support modifying the tree itself; it is suitable
/// for use in indices.
///
/// After a path of this kind has been created, the original tree might mutated
/// in a way that invalidates the path, setting some of its weak references to
/// nil, or breaking the consistency of its trail of slot indices. The path
/// checks for this during navigation, and traps if it finds itself invalidated.
///
@usableFromInline
@_fixed_layout
internal struct _BTreeWeakPath<Key: Comparable, Value>: _BTreePath {
  @usableFromInline
  @_fixed_layout
  struct Weak<T: AnyObject> {
    @usableFromInline
    weak var value: T?

    @inlinable
    init(_ value: T) {
      self.value = value
    }
  }

  @usableFromInline
  typealias Node = _BTreeNode<Key, Value>

  @usableFromInline
  var _root: Weak<Node>
  @usableFromInline
  var offset: Int

  @usableFromInline
  var _path: [Weak<Node>]
  @usableFromInline
  var _slots: [Int]
  @usableFromInline
  var _node: Weak<Node>
  @usableFromInline
  var slot: Int?

  @inlinable
  init(root: Node) {
    self._root = Weak(root)
    self.offset = root.count
    self._path = []
    self._slots = []
    self._node = Weak(root)
    self.slot = nil
  }

  @inlinable
  var root: Node {
    guard let root = _root.value else { invalid() }
    return root
  }
  @inlinable
  var count: Int { return root.count }
  @inlinable
  var length: Int { return _path.count + 1}

  @inlinable
  var node: Node {
    guard let node = _node.value else { invalid() }
    return node
  }

  @inlinable
  internal func expectRoot(_ root: Node) {
    expectValid(_root.value === root)
  }

  @inlinable
  internal func expectValid(
    _ expression: @autoclosure () -> Bool,
    file: StaticString = #file,
    line: UInt = #line
  ) {
    precondition(expression(), "Invalid _BTreeIndex", file: file, line: line)
  }

  @inlinable
  internal func invalid(
    _ file: StaticString = #file,
    line: UInt = #line
  ) -> Never {
    preconditionFailure("Invalid _BTreeIndex", file: file, line: line)
  }

  @inlinable
  internal mutating func popFromSlots() {
    assert(self.slot != nil)
    let node = self.node
    offset += node.count - node.offset(ofSlot: slot!)
    slot = nil
  }

  @inlinable
  internal mutating func popFromPath() {
    assert(_path.count > 0 && slot == nil)
    let child = node
    _node = _path.removeLast()
    expectValid(node.children[_slots.last!] === child)
    slot = _slots.removeLast()
  }

  @inlinable
  internal mutating func pushToPath() {
    assert(self.slot != nil)
    let child = node.children[slot!]
    _path.append(_node)
    _node = Weak(child)
    _slots.append(slot!)
    slot = nil
  }

  @inlinable
  internal mutating func pushToSlots(_ slot: Int, offsetOfSlot: Int) {
    assert(self.slot == nil)
    offset -= node.count - offsetOfSlot
    self.slot = slot
  }

  @inlinable
  func forEach(ascending: Bool, body: (Node, Int) -> Void) {
    if ascending {
      var child: Node? = node
      body(child!, slot!)
      for i in (0 ..< _path.count).reversed() {
        guard let node = _path[i].value else { invalid() }
        let slot = _slots[i]
        expectValid(node.children[slot] === child)
        child = node
        body(node, slot)
      }
    } else {
      for i in 0 ..< _path.count {
        guard let node = _path[i].value else { invalid() }
        let slot = _slots[i]
        let value = i < _path.count - 1
          ? _path[i + 1].value
          : _node.value
        expectValid(node.children[slot] === value)
        body(node, slot)
      }
      body(node, slot!)
    }
  }

  @inlinable
  func forEachSlot(ascending: Bool, body: (Int) -> Void) {
    if ascending {
      body(slot!)
      _slots.reversed().forEach(body)
    } else {
      _slots.forEach(body)
      body(slot!)
    }
  }
}

/// A mutable path in a B-tree, holding strong references to nodes on the path.
/// This path variant does not support modifying the tree itself; it is suitable
/// for use in generators.
@usableFromInline
@_fixed_layout
internal struct _BTreeStrongPath<Key: Comparable, Value>: _BTreePath {
  @usableFromInline
  typealias Node = _BTreeNode<Key, Value>

  @usableFromInline
  var root: Node
  @usableFromInline
  var offset: Int

  @usableFromInline
  var _path: [Node]
  @usableFromInline
  var _slots: [Int]
  @usableFromInline
  var node: Node
  @usableFromInline
  var slot: Int?

  @inlinable
  init(root: Node) {
    self.root = root
    self.offset = root.count
    self._path = []
    self._slots = []
    self.node = root
    self.slot = nil
  }

  @inlinable
  var count: Int { return root.count }
  @inlinable
  var length: Int { return _path.count + 1 }

  @inlinable
  mutating func popFromSlots() {
    assert(self.slot != nil)
    offset += node.count - node.offset(ofSlot: slot!)
    slot = nil
  }

  @inlinable
  mutating func popFromPath() {
    assert(_path.count > 0 && slot == nil)
    node = _path.removeLast()
    slot = _slots.removeLast()
  }

  @inlinable
  mutating func pushToPath() {
    assert(slot != nil)
    let child = node.children[slot!]
    _path.append(node)
    node = child
    _slots.append(slot!)
    slot = nil
  }

  @inlinable
  mutating func pushToSlots(_ slot: Int, offsetOfSlot: Int) {
    assert(self.slot == nil)
    offset -= node.count - offsetOfSlot
    self.slot = slot
  }

  @inlinable
  func forEach(ascending: Bool, body: (Node, Int) -> Void) {
    if ascending {
      body(node, slot!)
      for i in (0 ..< _path.count).reversed() {
        body(_path[i], _slots[i])
      }
    } else {
      for i in 0 ..< _path.count {
        body(_path[i], _slots[i])
      }
      body(node, slot!)
    }
  }

  @inlinable
  func forEachSlot(ascending: Bool, body: (Int) -> Void) {
    if ascending {
      body(slot!)
      _slots.reversed().forEach(body)
    } else {
      _slots.forEach(body)
      body(slot!)
    }
  }
}

extension _BTree {
  // MARK: Cursors

  @usableFromInline
  internal typealias Cursor = _BTreeCursor<Key, Value>

  /// Call `body` with a cursor at `offset` in this tree.
  ///
  /// - Warning: Do not rely on anything about `self` (the `_BTree` that is the
  ///   target of this method) during the execution of body: it will not appear
  ///   to have the correct value. Instead, use only the supplied cursor to
  ///   manipulate the tree.
  ///
  @inlinable
  internal mutating func withCursor<R>(
    atOffset offset: Int,
    body: (Cursor) throws -> R
  ) rethrows -> R {
    precondition(offset >= 0 && offset <= count)
    makeUnique()
    let cursor = _BTreeCursor(_BTreeCursorPath(root: root, offset: offset))
    root = Node(order: self.order)
    defer { self.root = cursor.finish() }
    return try body(cursor)
  }

  /// Call `body` with a cursor at the start of this tree.
  ///
  /// - Warning: Do not rely on anything about `self` (the `_BTree` that is the
  ///   target of this method) during the execution of body: it will not appear
  ///   to have the correct value. Instead, use only the supplied cursor to
  ///   manipulate the tree.
  ///
  @inlinable
  internal mutating func withCursorAtStart<R>(
    _ body: (Cursor) throws -> R
  ) rethrows -> R {
    return try withCursor(atOffset: 0, body: body)
  }

  /// Call `body` with a cursor at the end of this tree.
  ///
  /// - Warning: Do not rely on anything about `self` (the `_BTree` that is the
  ///   target of this method) during the execution of body: it will not appear
  ///   to have the correct value. Instead, use only the supplied cursor to
  ///   manipulate the tree.
  ///
  @inlinable
  internal mutating func withCursorAtEnd<R>(
    _ body: (Cursor) throws -> R
  ) rethrows -> R {
    makeUnique()
    let cursor = _BTreeCursor(_BTreeCursorPath(endOf: root))
    root = Node(order: self.order)
    defer { self.root = cursor.finish() }
    return try body(cursor)
  }

  /// Call `body` with a cursor positioned on `key` in this tree.
  /// If there are multiple elements with the same key, `selector` indicates
  /// which matching element to find.
  ///
  /// - Warning: Do not rely on anything about `self` (the `_BTree` that is the
  ///   target of this method) during the execution of body: it will not appear
  ///   to have the correct value. Instead, use only the supplied cursor to
  ///   manipulate the tree.
  ///
  @inlinable
  internal mutating func withCursor<R>(
    onKey key: Key,
    choosing selector: _BTreeKeySelector = .any,
    body: (Cursor) throws -> R
  ) rethrows -> R {
    makeUnique()
    let cursor = _BTreeCursor(_BTreeCursorPath(
      root: root, key: key, choosing: selector))
    root = Node(order: self.order)
    defer { self.root = cursor.finish() }
    return try body(cursor)
  }

  /// Call `body` with a cursor positioned on `index` in this tree.
  ///
  /// - Warning: Do not rely on anything about `self` (the `_BTree` that is the
  ///   target of this method) during the
  ///   execution of body: it will not appear to have the correct value.
  ///   Instead, use only the supplied cursor to manipulate the tree.
  ///
  @inlinable
  internal mutating func withCursor<R>(
    at index: Index,
    body: (Cursor) throws -> R
  ) rethrows -> R {
    index.state.expectRoot(root)
    makeUnique()
    let cursor = _BTreeCursor(_BTreeCursorPath(
      root: root, slotsFrom: index.state))
    root = Node(order: self.order)
    defer { self.root = cursor.finish() }
    return try body(cursor)
  }
}

/// A mutable path in a B-tree, holding strong references to nodes on the path.
/// This path variant supports modification of the tree itself.
///
/// To speed up operations inserting/removing individual elements from the tree,
/// this path keeps the tree in a special editing state, with element counts of
/// nodes on the current path subtracted from their ancestors' counts. The
/// counts are restored when the path ascends back towards the root.
///
/// Because this preparation breaks the tree's invariants, there should not be
/// references to the tree's root outside of the cursor. Creating a
/// `_BTreeCursorPath` for a tree takes exclusive ownership of its root for the
/// duration of the editing. (I.e., until `finish()` is called.) If the root
/// isn't uniquely held, you'll need to clone it before creating a cursor path
/// on it. (The path clones internal nodes on its own, as needed.)
///
@usableFromInline
@_fixed_layout
internal struct _BTreeCursorPath<Key: Comparable, Value>: _BTreePath {
  @usableFromInline
  typealias Tree = _BTree<Key, Value>
  @usableFromInline
  typealias Node = _BTreeNode<Key, Value>
  @usableFromInline
  typealias Element = (key: Key, value: Value)

  /// The root node in the tree that is being edited. Note that this isn't a
  /// valid B-tree while the cursor is active: each node on the current path has
  /// an invalid `count` field. (Other B-tree invariants are kept, though.)
  @usableFromInline
  var root: Node

  /// The current count of elements in the tree. This is always kept up to date,
  /// while `root.count` is usually invalid.
  @usableFromInline
  var count: Int

  /// The offset of the currently focused element in the tree.
  @usableFromInline
  var offset: Int

  /// The current path in the tree that is being edited.
  ///
  /// Only the last node on the path has correct `count`; the element count of
  /// the currently focused descendant subtree is subtracted from each
  /// ancestor's count. I.e:
  ///     `path[i].count = realCount(path[i]) - realCount(path[i+1])`.
  @usableFromInline
  var _path: [Node]
  @usableFromInline
  var node: Node

  /// The slots on the path to the currently focused part of the tree.
  @usableFromInline
  var _slots: [Int]
  @usableFromInline
  var slot: Int?

  @inlinable
  init(root: Node) {
    self.root = root
    self.offset = root.count
    self.count = root.count
    self._path = []
    self.node = root
    self._slots = []
    self.slot = nil
  }

  @inlinable
  var length: Int { return _path.count + 1}

  @inlinable
  var element: Element {
    get { return node.elements[slot!] }
    set { node.elements[slot!] = newValue }
  }

  @inlinable
  var key: Key {
    get { return node.elements[slot!].0 }
    set { node.elements[slot!].0 = newValue }
  }

  @inlinable
  var value: Value {
    get { return node.elements[slot!].1 }
    set { node.elements[slot!].1 = newValue }
  }

  @inlinable
  func setValue(_ value: Value) -> Value {
    precondition(!isAtEnd)
    let old = node.elements[slot!].1
    node.elements[slot!].1 = value
    return old
  }

  /// Invalidate this cursor.
  @inlinable
  mutating func invalidate() {
    root = _BTreeNode<Key, Value>(order: root.order)
    count = 0
    offset = 0
    _path = []
    node = root
    _slots = []
    slot = nil
  }

  @inlinable
  mutating func popFromSlots() {
    assert(self.slot != nil)
    offset += node.count - node.offset(ofSlot: slot!)
    slot = nil
  }

  @inlinable
  mutating func popFromPath() {
    assert(_path.count > 0 && slot == nil)
    let child = node
    node = _path.removeLast()
    node.count += child.count
    slot = _slots.removeLast()
  }

  @inlinable
  mutating func pushToPath() {
    assert(self.slot != nil)
    let parent = node
    _path.append(parent)
    node = parent.makeChildUnique(self.slot!)
    parent.count -= node.count
    _slots.append(slot!)
    slot = nil
  }

  @inlinable
  mutating func pushToSlots(_ slot: Int, offsetOfSlot: Int) {
    assert(self.slot == nil)
    offset -= node.count - offsetOfSlot
    self.slot = slot
  }

  @inlinable
  func forEach(ascending: Bool, body: (Node, Int) -> Void) {
    if ascending {
      body(node, slot!)
      for i in (0 ..< _path.count).reversed() {
        body(_path[i], _slots[i])
      }
    } else {
      for i in 0 ..< _path.count {
        body(_path[i], _slots[i])
      }
      body(node, slot!)
    }
  }

  @inlinable
  func forEachSlot(ascending: Bool, body: (Int) -> Void) {
    if ascending {
      body(slot!)
      _slots.reversed().forEach(body)
    } else {
      _slots.forEach(body)
      body(slot!)
    }
  }

  @inlinable
  mutating func finish() -> Node {
    var childCount = self.node.count
    while !_path.isEmpty {
      let node = _path.removeLast()
      node.count += childCount
      childCount = node.count
    }
    assert(root.count == count)
    defer { invalidate() }
    return root
  }

  /// Restore B-tree invariants after a single-element insertion produced an
  /// oversize leaf node.
  @inlinable
  internal mutating func fixupAfterInsert() {
    guard node.isTooLarge else { return }

    _path.append(self.node)
    _slots.append(self.slot!)

    // Split nodes on the way to the root until we restore the B-tree's size
    // constraints.
    var i = _path.count - 1
    while _path[i].isTooLarge {
      // Split path[i], which must have correct count.
      let left = _path[i]
      let slot = _slots[i]
      let splinter = left.split()
      let right = splinter.node
      if slot > left.elements.count {
        // Focused element is in the new branch; adjust self accordingly.
        _slots[i] = slot - left.elements.count - 1
        _path[i] = right
      } else if slot == left.elements.count && i == _path.count - 1 {
        // Focused element is the new separator; adjust self accordingly.
        _path.removeLast()
        _slots.removeLast()
      }

      if i > 0 {
        // Insert splinter into parent node and fix its count field.
        let parent = _path[i - 1]
        let pslot = _slots[i - 1]
        parent.insert(splinter, inSlot: pslot)
        parent.count += left.count + right.count + 1
        if slot > left.elements.count {
          // Focused element is in the new branch; update parent slot
          // accordingly.
          _slots[i - 1] = pslot + 1
        }
        i -= 1
      } else {
        // Create new root node.
        self.root = _BTreeNode<Key, Value>(
          left: left,
          separator: splinter.separator,
          right: right)
        _path.insert(self.root, at: 0)
        _slots.insert(slot > left.elements.count ? 1 : 0, at: 0)
      }
    }

    // Size constraints are now OK, but counts on path have become valid, so we
    // need to restore cursor state by subtracting focused children.
    while i < _path.count - 1 {
      _path[i].count -= _path[i + 1].count
      i += 1
    }

    node = _path.removeLast()
    slot = _slots.removeLast()
  }
}

/// A stateful editing interface for efficiently inserting/removing/updating a
/// range of elements in a B-tree.
///
/// Creating a cursor over a tree takes exclusive ownership of it; the tree is
/// in a transient invalid state while the cursor is active. (In particular,
/// element counts are not finalized until the cursor is deactivated.)
///
/// The cursor always focuses on a particular spot on the tree: either a
/// particular element, or the empty spot after the last element. There are
/// methods to move the cursor to the next or previous element, to modify the
/// currently focused element, to insert a new element before the current
/// position, and to remove the currently focused element from the tree.
///
/// Note that the cursor does not verify that keys you insert/modify uphold tree
/// invariants -- it is your responsibility to guarantee keys remain in
/// ascending order while you're working with the cursor.
///
/// Creating a cursor takes O(log *n*) steps; once the cursor has been created,
/// the complexity of most manipulations is amortized O(1). For example,
/// appending *k* new elements without a cursor takes O(*k* * log *n*) steps;
/// using a cursor to do the same only takes O(log *n* + *k*).
@usableFromInline
@_fixed_layout
internal final class _BTreeCursor<Key: Comparable, Value> {
  @usableFromInline
  internal typealias Element = (key: Key, value: Value)
  @usableFromInline
  internal typealias Tree = _BTree<Key, Value>
  @usableFromInline
  internal typealias Node = _BTreeNode<Key, Value>
  @usableFromInline
  internal typealias State = _BTreeCursorPath<Key, Value>

  @usableFromInline
  internal var state: State

  /// The number of elements in the tree currently being edited.
  @usableFromInline
  internal var count: Int { return state.count }

  /// The offset of the currently focused element in the tree.
  ///
  /// - Complexity: O(1) for the getter, O(log *n*) for the setter, where *n* is
  ///   the length of the tree.
  @inlinable
  internal var offset: Int {
    get {
      return state.offset
    }
    set {
      state.move(toOffset: newValue)
    }
  }

  // MARK: Simple properties

  /// Return true iff this is a valid cursor.
  @inlinable
  internal var isValid: Bool { return state.isValid }
  /// Return true iff the cursor is focused on the initial element.
  @inlinable
  internal var isAtStart: Bool { return state.isAtStart }
  /// Return true iff the cursor is focused on the spot beyond the last element.
  @inlinable
  internal var isAtEnd: Bool { return state.isAtEnd }

  // MARK: Initializers

  @inlinable
  internal init(_ state: _BTreeCursorPath<Key, Value>) {
    self.state = state
  }

  // MARK: Finishing

  /// Finalize editing the tree and return it, deactivating this cursor.
  /// You'll need to create a new cursor to continue editing the tree.
  ///
  /// - Complexity: O(log *n*), where *n* is the length of the tree
  @inlinable
  internal func finish() -> Node {
    return state.finish()
  }

  // MARK: Navigation

  /// Position the cursor on the next element in the B-tree.
  ///
  /// - Requires: `!isAtEnd`
  /// - Complexity: Amortized O(1)
  @inlinable
  internal func moveForward() {
    state.moveForward()
  }

  /// Position this cursor on the previous element in the B-tree.
  ///
  /// - Requires: `!isAtStart`
  /// - Complexity: Amortized O(1)
  @inlinable
  internal func moveBackward() {
    state.moveBackward()
  }

  /// Position this cursor on the start of the B-tree.
  ///
  /// - Complexity: O(log *m*), where *m* is `offset`
  @inlinable
  internal func moveToStart() {
    state.moveToStart()
  }

  /// Position this cursor on the end of the B-tree, i.e., at the offset after
  /// the last element.
  ///
  /// - Complexity: O(log(*n* - *m*)), where *n* is the length of the
  ///   tree and *m* is `offset`
  @inlinable
  internal func moveToEnd() {
    state.moveToEnd()
  }

  /// Move this cursor to the specified offset in the B-tree.
  ///
  /// - Complexity: O(log(*distance*)), where *distance* is the absolute
  ///   difference between the desired and current offsets.
  @inlinable
  internal func move(toOffset offset: Int) {
    state.move(toOffset: offset)
  }

  /// Move this cursor to an element with the specified key.
  /// If there are no such elements, the cursor is moved to the first element
  /// after `key` (or at the end of tree). If there are multiple such elements,
  /// `selector` specifies which one to find.
  ///
  /// - Complexity: O(log *n*), where *n* is the length of the tree
  @inlinable
  internal func move(to key: Key, choosing selector: _BTreeKeySelector = .any) {
    state.move(to: key, choosing: selector)
  }

  // MARK: Editing

  /// Get or replace the currently focused element.
  ///
  /// - Warning: Changing the key is potentially dangerous; it is the caller's
  ///   responsibility to ensure that keys remain in ascending order. This is
  ///   not verified at runtime.
  /// - Complexity: O(1)
  @inlinable
  internal var element: Element {
    get { return state.element }
    set { state.element = newValue }
  }

  /// Get or set the key of the currently focused element.
  ///
  /// - Warning: Changing the key is potentially dangerous; it is the caller's
  ///   responsibility to ensure that keys remain in ascending order. This is
  ///   not verified at runtime.
  /// - Complexity: O(1)
  @inlinable
  internal var key: Key {
    get { return state.key }
    set { state.key = newValue }
  }

  /// Get or set the value of the currently focused element.
  ///
  /// - Complexity: O(1)
  @inlinable
  internal var value: Value {
    get { return state.value }
    set { state.value = newValue }
  }

  /// Update the value stored at the cursor's current position and return the
  /// previous value. This method does not change the cursor's position.
  ///
  /// - Complexity: O(1)
  @inlinable
  internal func setValue(_ value: Value) -> Value {
    return state.setValue(value)
  }

  /// Insert a new element after the cursor's current position, and position the
  /// cursor on the new element.
  ///
  /// - Complexity: amortized O(1)
  @inlinable
  internal func insertAfter(_ element: Element) {
    precondition(!self.isAtEnd)
    state.count += 1
    if state.node.isLeaf {
      let slot = state.slot!
      state.node.insert(element, inSlot: slot + 1)
      state.slot = slot + 1
      state.offset += 1
    } else {
      moveForward()
      assert(state.node.isLeaf && state.slot == 0)
      state.node.insert(element, inSlot: 0)
    }
    state.fixupAfterInsert()
  }

  /// Insert a new element at the cursor's current offset, and leave the cursor
  /// positioned on the original element.
  ///
  /// - Complexity: amortized O(1)
  @inlinable
  internal func insert(_ element: Element) {
    precondition(self.isValid)
    state.count += 1
    if state.node.isLeaf {
      state.node.insert(element, inSlot: state.slot!)
    } else {
      moveBackward()
      assert(state.node.isLeaf && state.slot == state.node.elements.count - 1)
      state.node.append(element)
      state.slot = state.node.elements.count - 1
      state.offset += 1
    }
    state.fixupAfterInsert()
    moveForward()
  }

  /// Insert the contents of `tree` before the currently focused element,
  /// keeping the cursor's position on it.
  ///
  /// - Complexity: O(log(*n* + *m*)), where *n* is the length of the
  ///   tree and *m* is the length of the given tree
  @inlinable
  internal func insert(_ tree: Tree) {
    insert(tree.root)
  }

  /// Insert the contents of `node` before the currently focused element,
  /// keeping the cursor's position on it.
  ///
  /// - Complexity: O(log(*n* + *m*), where *n* is the length of the
  ///   tree and *m* is the length of the given node
  @inlinable
  internal func insert(_ node: Node) {
    insertWithoutCloning(node.clone())
  }

  /// Insert all elements in a sequence before the currently focused element,
  /// keeping the cursor's position on it.
  ///
  /// - Requires: `self.isValid` and `elements` is sorted by key.
  /// - Complexity: O(log *n* + *m*), , where *n* is the length of the tree
  ///   and *m* is the number of elements in the sequence.
  @inlinable
  internal func insert<S: Sequence>(_ elements: S) where S.Element == Element {
    insertWithoutCloning(_BTree(sortedElements: elements).root)
  }

  @inlinable
  internal func insertWithoutCloning(_ root: Node) {
    precondition(isValid)
    let c = root.count
    if c == 0 { return }
    if c == 1 {
      insert(root.elements[0])
      return
    }
    if self.count == 0 {
      state = State(endOf: root)
      return
    }

    let offset = self.offset
    if offset == self.count {
      // Append
      moveBackward()
      let separator = remove()
      let j = Node.join(
        left: finish(),
        separator: separator,
        right: root)
      state = State(endOf: j)
    } else if offset == 0 {
      // Prepend
      let separator = remove()
      let j = Node.join(
        left: root,
        separator: separator,
        right: finish())
      state = State(root: j, offset: offset + c)
    } else {
      // Insert in middle
      moveBackward()
      let sep1 = remove()
      let (prefix, sep2, suffix) = state.split()
      state.invalidate()
      let t1 = Node.join(
        left: prefix.root,
        separator: sep1,
        right: root)
      let t2 = Node.join(
        left: t1,
        separator: sep2,
        right: suffix.root)
      state = State(root: t2, offset: offset + c)
    }
  }

  /// Remove and return the element at the cursor's current position, and
  /// position the cursor on its successor.
  ///
  /// - Complexity: O(log *n*), where *n* is the length of the tree
  @inlinable
  @discardableResult
  internal func remove() -> Element {
    precondition(!isAtEnd)
    let result = state.element
    if !state.node.isLeaf {
      // For internal nodes, remove the (leaf) predecessor instead, then put it
      // back in place of the element that we actually want to remove.
      moveBackward()
      let surrogate = remove()
      self.key = surrogate.0
      self.value = surrogate.1
      moveForward()
      return result
    }
    let targetOffset = self.offset
    state.node.elements.remove(at: state.slot!)
    state.node.count -= 1
    state.count -= 1
    state.popFromSlots()

    while state.node !== state.root && state.node.isTooSmall {
      state.popFromPath()
      let slot = state.slot!
      state.popFromSlots()
      state.node.fixDeficiency(slot)
    }
    while targetOffset != count
      && targetOffset == self.offset
      && state.node !== state.root {
        state.popFromPath()
        state.popFromSlots()
    }
    if state.node === state.root
      && state.node.elements.count == 0
      && state.node.children.count == 1 {
      assert(state.length == 1 && state.slot == nil)
      state.root = state.node.makeChildUnique(0)
      state.node = state.root
    }
    state.descend(toOffset: targetOffset)
    return result
  }

  /// Remove `n` elements starting at the cursor's current position, and
  /// position the cursor on the successor of the last element that was removed.
  ///
  /// - Complexity: O(log *n*), where *n* is the length of the tree.
  @inlinable
  internal func remove(_ n: Int) {
    precondition(isValid && n >= 0 && self.offset + n <= count)
    if n == 0 { return }
    if n == 1 { remove(); return }
    if n == count { removeAll(); return }

    let offset = self.offset

    if offset == 0 {
      state.move(toOffset: n - 1)
      state = State(startOf: state.suffix().root)
    } else if offset == count - n {
      state = State(endOf: state.prefix().root)
    } else {
      let left = state.prefix()
      state.move(toOffset: offset + n)
      let separator = state.element
      let right = state.suffix()
      state.invalidate()
      let j = Node.join(
        left: left.root,
        separator: separator,
        right: right.root)
      state = State(root: j, offset: offset)
    }
  }

  /// Remove all elements.
  ///
  /// - Complexity: O(log *n*) if nodes of this tree are shared with other
  ///   trees; O(*n*) otherwise, where *n* is the length of the tree.
  @inlinable
  internal func removeAll() {
    state = State(startOf: Node(order: state.root.order))
  }

  /// Remove all elements before (and if `inclusive` is true, including) the
  /// current position, and position the cursor at the start of the remaining
  /// tree.
  ///
  /// - Complexity: O(log *n*) if nodes of this tree are shared with other
  ///   trees; O(*n*) otherwise, where *n* is the length of the tree.
  @inlinable
  internal func removeAllBefore(includingCurrent inclusive: Bool) {
    if isAtEnd {
      assert(!inclusive)
      removeAll()
      return
    }
    if !inclusive {
      if isAtStart {
        return
      }
      moveBackward()
    }
    state = State(startOf: state.suffix().root)
  }

  /// Remove all elements before (and if `inclusive` is true, including) the
  /// current position, and position the cursor on the end of the remaining
  /// tree.
  ///
  /// - Complexity: O(log *n*) if nodes of this tree are shared with other
  ///   trees; O(*n*) otherwise, where *n* is the length of the tree.
  @inlinable
  internal func removeAllAfter(includingCurrent inclusive: Bool) {
    if isAtEnd {
      assert(!inclusive)
      return
    }
    if !inclusive {
      moveForward()
      if isAtEnd {
        return
      }
    }
    if isAtStart {
      removeAll()
      return
    }
    state = State(endOf: state.prefix().root)
  }

  /// Extract `n` elements starting at the cursor's current position, and
  /// position the cursor on the successor of the last element that was removed.
  ///
  /// - Returns: The extracted elements as a new B-tree.
  /// - Complexity: O(log *n*), where *n* is the length of the tree.
  @inlinable
  internal func extract(_ n: Int) -> Tree {
    precondition(isValid && n >= 0 && self.offset + n <= count)
    if n == 0 {
      return Tree(order: state.root.order)
    }
    if n == 1 {
      let element = remove()
      var tree = Tree(order: state.root.order)
      tree.insert(element)
      return tree
    }
    if n == count {
      let node = state.finish()
      state = State(startOf: Node(order: node.order))
      return Tree(node)
    }

    let offset = self.offset
    if offset == count - n {
      var split = state.split()
      state = State(root: split.prefix.root, offset: offset)
      split.suffix.insert(split.separator, atOffset: 0)
      return split.suffix
    }

    let (left, sep1, tail) = state.split()
    state = State(root: tail.root, offset: n - 1)
    var (mid, sep2, right) = state.split()
    state.invalidate()
    let j = Node.join(left: left.root, separator: sep2, right: right.root)
    state = State(root: j, offset: offset)
    mid.insert(sep1, atOffset: 0)
    return mid
  }
}
