//===--- BTreeBuilder.swift -----------------------------------*- swift -*-===//
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

extension _BTree {
  // MARK: Bulk loading initializers

  /// Create a new B-tree from elements of an unsorted sequence, using a stable
  /// sort algorithm.
  ///
  /// - Parameter elements: An unsorted sequence of arbitrary length.
  /// - Parameter order: The desired B-tree order. If not specified
  ///   (recommended), the default order is used.
  /// - Complexity: O(count * log(`count`))
  /// - SeeAlso: `init(sortedElements:order:fillFactor:)` for a (faster) variant
  ///   that can be used if the sequence is already sorted.
  @inlinable
  internal init<S: Sequence>(
    _ elements: S,
    dropDuplicates: Bool = false,
    order: Int? = nil
  ) where S.Element == Element {
    let order = order ?? Node.defaultOrder
    self.init(Node(order: order))
    withCursorAtEnd { cursor in
      for element in elements {
        cursor.move(to: element.0, choosing: .last)
        let match = !cursor.isAtEnd && cursor.key == element.0
        if match {
          if dropDuplicates {
            cursor.element = element
          } else {
            cursor.insertAfter(element)
          }
        } else {
          cursor.insert(element)
        }
      }
    }
  }

  /// Create a new B-tree from elements of a sequence sorted by key.
  ///
  /// - Parameter sortedElements: A sequence of arbitrary length, sorted by key.
  /// - Parameter order: The desired B-tree order. If not specified
  ///   (recommended), the default order is used.
  /// - Parameter fillFactor: The desired fill factor in each node of the new
  ///   tree. Must be between 0.5 and 1.0. If not specified, a value of 1.0 is
  ///   used, i.e., nodes will be loaded with as many elements as possible.
  /// - Complexity: O(*n*), where *n* is the length of the sequence.
  /// - SeeAlso: `init(elements:order:fillFactor:)` for a (slower) unsorted
  ///   variant.
  @inlinable
  internal init<S: Sequence>(
    sortedElements elements: S,
    dropDuplicates: Bool = false,
    order: Int? = nil,
    fillFactor: Double = 1
  ) where S.Element == Element {
    var iterator = elements.makeIterator()
    self.init(
      order: order ?? Node.defaultOrder, fillFactor: fillFactor,
      dropDuplicates: dropDuplicates, next: { iterator.next() })
  }

  @inlinable
  internal init(
    order: Int,
    fillFactor: Double = 1,
    dropDuplicates: Bool = false,
    next: () -> Element?
  ) {
    precondition(order > 1)
    precondition(fillFactor >= 0.5 && fillFactor <= 1)
    let keysPerNode = Int(fillFactor * Double(order - 1) + 0.5)
    assert(keysPerNode >= (order - 1) / 2 && keysPerNode <= order - 1)

    var builder = _BTreeBuilder<Key, Value>(
      order: order, keysPerNode: keysPerNode)
    if dropDuplicates {
      guard var buffer = next() else {
        self.init(Node(order: order))
        return
      }
      while let element = next() {
        precondition(buffer.0 <= element.0)
        if buffer.0 < element.0 {
          builder.append(buffer)
        }
        buffer = element
      }
      builder.append(buffer)
    } else {
      var lastKey: Key? = nil
      while let element = next() {
        precondition(lastKey == nil || lastKey! <= element.0)
        lastKey = element.0
        builder.append(element)
      }
    }
    self.init(builder.finish())
  }
}

@usableFromInline
internal enum BuilderState {
  /// The builder needs a separator element.
  case separator
  /// The builder is filling up a seedling node.
  case element
}

/// A construct for efficiently building a fully loaded B-tree from a series of
/// elements.
///
/// The bulk loading algorithm works growing a line of perfectly loaded
/// saplings, in order of decreasing depth, with a separator element between
/// each of them.
///
/// Added elements are collected into a separator and a new leaf node (called
/// the "seedling"). When the seedling becomes full it is appended to or
/// recursively merged into the list of saplings.
///
/// When `finish` is called, the final list of saplings plus the last partial
/// seedling is joined into a single tree, which becomes the root.
@usableFromInline
@_fixed_layout
internal struct _BTreeBuilder<Key: Comparable, Value> {
  @usableFromInline
  typealias Node = _BTreeNode<Key, Value>
  @usableFromInline
  typealias Element = Node.Element
  @usableFromInline
  typealias Splinter = Node.Splinter

  @usableFromInline
  internal var order: Int //FIXME: was let, but got complaints about direct init
  @usableFromInline
  internal var keysPerNode: Int //FIXME: was let, see `order` above
  @usableFromInline
  internal var saplings: [Node]
  @usableFromInline
  internal var separators: [Element]
  @usableFromInline
  internal var seedling: Node
  @usableFromInline
  internal var state: BuilderState

  @inlinable
  init(order: Int) {
    self.init(order: order, keysPerNode: order - 1)
  }

  @inlinable
  init(order: Int, keysPerNode: Int) {
    precondition(order > 1)
    precondition(keysPerNode >= (order - 1) / 2 && keysPerNode <= order - 1)

    self.order = order
    self.keysPerNode = keysPerNode
    self.saplings = []
    self.separators = []
    self.seedling = Node(order: order)
    self.state = .element
  }

  @inlinable
  var lastKey: Key? {
    switch state {
    case .separator:
      return saplings.last?.last?.0
    case .element:
      return seedling.last?.0 ?? separators.last?.0
    @unknown default:
      fatalError("unhandled unknown case")
    }
  }

  @inlinable
  func isValidNextKey(_ key: Key) -> Bool {
    guard let last = lastKey else { return true }
    return last <= key
  }

  @inlinable
  mutating func append(_ element: Element) {
    assert(isValidNextKey(element.0))
    switch state {
    case .separator:
      separators.append(element)
      state = .element
    case .element:
      seedling.append(element)
      if seedling.count == keysPerNode {
        closeSeedling()
        state = .separator
      }
    @unknown default:
      fatalError("unhandled unknown case")
    }
  }

  @inlinable
  internal mutating func closeSeedling() {
    append(sapling: seedling)
    seedling = Node(order: order)
  }

  @inlinable
  mutating func append(_ node: Node) {
    appendWithoutCloning(node.clone())
  }

  @inlinable
  mutating func appendWithoutCloning(_ node: Node) {
    assert(node.order == order)
    if node.isEmpty { return }
    assert(isValidNextKey(node.first!.0))
    if node.depth == 0 {
      if state == .separator {
        assert(seedling.isEmpty)
        separators.append(node.elements.removeFirst())
        node.count -= 1
        state = .element
        if node.isEmpty { return }
        seedling = node
      } else if seedling.count > 0 {
        let sep = seedling.elements.removeLast()
        seedling.count -= 1
        if let splinter = seedling.shiftSlots(
          separator: sep, node: node, target: keysPerNode) {
          closeSeedling()
          separators.append(splinter.separator)
          seedling = splinter.node
        }
      } else {
        seedling = node
      }
      if seedling.count >= keysPerNode {
        closeSeedling()
        state = .separator
      }
      return
    }

    if state == .element && seedling.count > 0 {
      let sep = seedling.elements.removeLast()
      seedling.count -= 1
      closeSeedling()
      separators.append(sep)
    }
    if state == .separator {
      let cursor = _BTreeCursor(_BTreeCursorPath(endOf: saplings.removeLast()))
      cursor.moveBackward()
      let separator = cursor.remove()
      saplings.append(cursor.finish())
      separators.append(separator)
    }
    assert(seedling.isEmpty)
    append(sapling: node)
    state = .separator
  }

  @inlinable
  mutating func append(sapling: Node) {
    var sapling = sapling
    while !saplings.isEmpty {
      assert(saplings.count == separators.count)
      var previous = saplings.removeLast()
      let separator = separators.removeLast()

      // Join previous saplings together until they grow at least as deep as the
      // new one.
      while previous.depth < sapling.depth {
        if saplings.isEmpty {
          // If the single remaining sapling is too shallow, just join it to the
          // new sapling and call it a day.
          saplings.append(Node.join(
            left: previous, separator: separator, right: sapling))
          return
        }
        previous = Node.join(
          left: saplings.removeLast(),
          separator: separators.removeLast(),
          right: previous)
      }

      let fullPrevious = previous.elements.count >= keysPerNode
      let fullSapling = sapling.elements.count >= keysPerNode

      if previous.depth == sapling.depth + 1 && !fullPrevious && fullSapling {
        // Graft node under the last sapling, as a new child branch.
        previous.elements.append(separator)
        previous.children.append(sapling)
        previous.count += sapling.count + 1
        sapling = previous
      } else if previous.depth == sapling.depth && fullPrevious && fullSapling {
        // We have two full nodes; add them as two branches of a new, deeper
        // node.
        sapling = Node(
          left: previous, separator: separator, right: sapling)
      } else if previous.depth > sapling.depth || fullPrevious {
        // The new sapling can be appended to the line and we're done.
        saplings.append(previous)
        separators.append(separator)
        break
      } else if let splinter = previous.shiftSlots(
        separator: separator, node: sapling, target: keysPerNode) {
        // We have made the previous sapling full; add it as a new one before
        // trying again with the remainder.
        assert(previous.elements.count == keysPerNode)
        append(sapling: previous)
        separators.append(splinter.separator)
        sapling = splinter.node
      } else {
        // We've combined the two saplings; try again with the result.
        sapling = previous
      }
    }
    saplings.append(sapling)
  }

  @inlinable
  mutating func finish() -> Node {
    // Merge all saplings and the seedling into a single tree.
    var root: Node
    if separators.count == saplings.count - 1 {
      assert(seedling.count == 0)
      root = saplings.removeLast()
    } else {
      root = seedling
    }
    assert(separators.count == saplings.count)
    while !saplings.isEmpty {
      root = Node.join(
        left: saplings.removeLast(),
        separator: separators.removeLast(),
        right: root)
    }
    state = .element
    return root
  }
}

/// The matching strategy to use when comparing elements from two trees with
/// duplicate keys.
@usableFromInline
internal enum _BTreeMatchingStrategy {

  /// Use a matching strategy appropriate for a set. I.e., match partition
  /// classes over key equality rather than individual keys.
  ///
  /// This strategy ignores the multiplicity of keys, and only considers whether
  /// a key is included in the two trees at all.
  /// E.g., a single element from one tree will be considered a match for any
  /// positive number of elements with the same key in the other tree.
  case groupingMatches

  /// Use a matching strategy appropriate for a multiset. I.e., try to establish
  /// a one-to-one correspondence between elements from the two trees with equal
  /// keys.
  ///
  /// This strategy keeps track of the multiplicity of each key, and matches
  /// every element from one tree with at most a single element with an equal
  /// key from the other tree. If a key has different multiplicities in the two
  /// trees, duplicate elements above the lesser multiplicity will not be
  /// considered matching.
  case countingMatches
}

extension _BTree {
  /// Merge elements from two trees into a new tree, and return it.
  ///
  /// - Parameter other: Any tree with the same order as `self`.
  ///
  /// - Parameter strategy:
  ///      When `.groupingMatches`, elements in `self` whose keys also appear in
  ///      `other` are not included in the result. If neither input tree had
  ///      duplicate keys on its own, the result won't have any duplicates,
  ///      either.
  ///
  ///      When `.countingMatches`, all elements in both trees are kept in the
  ///      result, including ones with duplicate keys. The result may have
  ///      duplicate keys, even if the input trees only had unique-keyed
  ///      elements.
  ///
  /// - Returns: A tree with elements from `self` with matching keys in `other`
  ///   removed.
  ///
  /// - Note:
  ///     The elements of the two input trees may interleave and overlap in any
  ///     combination. However, if there are long runs of non-interleaved
  ///     elements, parts of the input trees will be entirely skipped instead of
  ///     elementwise processing. This may drastically improve performance.
  ///
  ///     When `strategy == .groupingMatches`, this function also detects shared
  ///     subtrees between the two trees, and links them directly into the
  ///     result when possible. (Otherwise matching keys are individually
  ///     processed.)
  ///
  /// - Requires: `self.order == other.order`
  ///
  /// - Complexity:
  ///    - O(min(*n*, *m*)) in general, where *n* is the
  ///      length of the tree and *m* is the length of the other tree.
  ///    - O(log(*n* + *m*)) if there are only a constant
  ///      amount of interleaving element runs, where *n* is the length of the
  ///      tree and *m* is the length of the other tree.
  @inlinable
  internal func union(
    _ other: _BTree,
    by strategy: _BTreeMatchingStrategy
  ) -> _BTree {
    var m = _BTreeMerger(first: self, second: other)
    switch strategy {
    case .groupingMatches:
      while !m.done {
        m.copyFromFirst(.excludingOtherKey)
        m.copyFromSecond(.excludingOtherKey)
        m.copyCommonElementsFromSecond()
      }
    case .countingMatches:
      while !m.done {
        m.copyFromFirst(.includingOtherKey)
        m.copyFromSecond(.excludingOtherKey)
      }
    @unknown default:
      fatalError("unhandled unknown case")
    }
    m.appendFirst()
    m.appendSecond()
    return m.finish()
  }

  /// Merge elements from other into this tree.
  ///
  /// - Parameter other: Any tree with the same order as `self`.
  ///
  /// - Parameter strategy:
  ///      A custom closure to determine a value to return based on values from
  ///      the same key.
  ///
  /// - Requires: `self.order == other.order`
  ///
  /// - Complexity: O(*m* * log *n*), where *n* is the
  ///   length of the tree and *m* is the length of the other tree.
  @inlinable
  internal mutating func formUnion(
    _ other: _BTree,
    by strategy: (Value, Value) -> Value
  ) {
    other.forEach { element -> Void in
      if let idx = index(forKey: element.key) {
        let o = offset(forKey: element.key)!
        self.setValue(atOffset: o, to: strategy(self[idx].value, element.value))
      } else {
        insert((element.key, element.value))
      }
    }
  }

  /// Merge elements from two trees and return it.
  ///
  /// - Parameter other: Any tree with the same order as `self`.
  ///
  /// - Parameter strategy:
  ///      A custom closure to determine a value to return based on values from
  ///      the same key.
  ///
  /// - Requires: `self.order == other.order`
  ///
  /// - Complexity: O(*m* * log *n*), where *n* is the
  ///   length of the tree and *m* is the length of the other tree.
  @inlinable
  internal func union(
    _ other: _BTree,
    by strategy: (Value, Value) -> Value
  ) -> _BTree {
    var result = self
    result.formUnion(other, by: strategy)
    return result
  }

  /// Merge elements from other into this tree.
  ///
  /// - Parameter other: Any tree with the same order as `self`.
  ///
  /// - Parameter strategy:
  ///      A custom closure to determine a value to return based on values from
  ///      the same key.
  ///
  /// - Requires: `self.order == other.order`
  ///
  /// - Complexity: O(*m* * log *n*), where *n* is the
  ///   length of the tree and *m* is the length of the other tree.
  @inlinable
  internal mutating func formUnion<S: Sequence>(
    _ other: S,
    by strategy: (Value, Value) -> Value
  ) where S.Element == (Key, Value) {
    var itr = other.makeIterator()

    while let it = itr.next() {
      if let idx = index(forKey: it.0) {
        let o = offset(forKey: it.0)!
        self.setValue(atOffset: o, to: strategy(self[idx].value, it.1))
      } else {
        insert(it)
      }
    }
  }

  /// Merge elements from other sequence into a tree with this trees elements
  /// and returns it.
  ///
  /// - Parameter other: Any tree with the same order as `self`.
  ///
  /// - Parameter strategy:
  ///      A custom closure to determine a value to return based on values from
  ///      the same key.
  ///
  /// - Requires: `self.order == other.order`
  ///
  /// - Complexity: O(*m* * log *n*), where *n* is the
  ///   length of the tree and *m* is the length of the other tree.
  @inlinable
  internal func union<S: Sequence>(
    _ other: S,
    by strategy: (Value, Value) -> Value
  ) -> _BTree where S.Element == (Key, Value) {
    var result = self
    result.formUnion(other, by: strategy)
    return result
  }

  /// Merge elements from other into this tree keeping duplicate keys.
  ///
  /// - Parameter other: Any tree with the same order as `self`.
  ///
  /// - Requires: `self.order == other.order`
  ///
  /// - Complexity: O(*m* * log *n*), where *n* is the
  ///   length of the tree and *m* is the length of the other tree.
  @inlinable
  internal mutating func formUnion<S: Sequence>(_ other: S)
  where S.Element == (Key, Value) {
    var itr = other.makeIterator()

    while let it = itr.next() {
      insert(it)
    }
  }

  /// Return a tree with the same elements as `self` except those with matching
  /// keys in `other`.
  ///
  /// - Parameter other: Any tree with the same order as `self`.
  ///
  /// - Parameter strategy:
  ///      When `.groupingMatches`, all elements in `self` that have a matching
  ///      key in `other` are removed.
  ///
  ///      When `.countingMatches`, for each key in `self`, only as many
  ///      matching elements are removed as the key's multiplicity in `other`.
  ///
  /// - Returns: A tree with elements from `self` with matching keys in `other`
  ///   removed.
  ///
  /// - Note:
  ///     The elements of the two input trees may interleave and overlap in any
  ///     combination. However, if there are long runs of non-interleaved
  ///     elements, parts of the input trees will be entirely skipped or linked
  ///     into the result instead of elementwise processing. This may
  ///     drastically improve performance.
  ///
  ///     This function also detects and skips over shared subtrees between the
  ///     two trees. (Keys that appear in both trees otherwise require
  ///     individual processing.)
  ///
  /// - Requires: `self.order == other.order`
  ///
  /// - Complexity:
  ///    - O(min(*n*, *m*)) in general, where *n* is the
  ///      length of the tree and *m* is the length of the other tree.
  ///    - O(log(*n* + *m*) if there are only a constant
  ///      amount of interleaving element runs, where *n* is the
  ///      length of the tree and *m* is the length of the other tree.
  @inlinable
  internal func subtracting(
    _ other: _BTree,
    by strategy: _BTreeMatchingStrategy
  ) -> _BTree {
    var m = _BTreeMerger(first: self, second: other)
    while !m.done {
      m.copyFromFirst(.excludingOtherKey)
      m.skipFromSecond(.excludingOtherKey)
      switch strategy {
      case .groupingMatches:
        m.skipCommonElements()
      case .countingMatches:
        m.skipMatchingNumberOfCommonElements()
      @unknown default:
        fatalError("unhandled unknown case")
      }
    }
    m.appendFirst()
    return m.finish()
  }

  /// Return a tree combining the elements of `self` and `other` except those
  /// whose keys can be matched in both trees.
  ///
  /// - Parameter other: Any tree with the same order as `self`.
  ///
  /// - Parameter strategy:
  ///      When `.groupingMatches`, all elements in both trees are removed whose
  ///      key appears in both trees, regardless of their multiplicities.
  ///
  ///      When `.countingMatches`, for each key, only as many matching elements
  ///      are removed as the minimum of the key's multiplicities in the two
  ///      trees, leaving "extra" occurences from the "longer" tree in the
  ///      result.
  ///
  /// - Returns: A tree combining elements of `self` and `other` except those
  ///   whose keys can be matched in both trees.
  ///
  /// - Note:
  ///     The elements of the two input trees may interleave and overlap in any
  ///     combination. However, if there are long runs of non-interleaved
  ///     elements, parts of the input trees will be entirely linked into the
  ///     result instead of elementwise processing. This may drastically improve
  ///     performance.
  ///
  ///     This function also detects and skips over shared subtrees between the
  ///     two trees. (Keys that appear in both trees otherwise require
  ///     individual processing.)
  ///
  /// - Requires: `self.order == other.order`
  ///
  /// - Complexity:
  ///    - O(min(*n*, *m*)) in general, where *n* is the
  ///      length of the tree and *m* is the length of the other tree.
  ///    - O(log(*n* + *m*) if there are only a constant
  ///      amount of interleaving element runs, where *n* is the
  ///      length of the tree and *m* is the length of the other tree.
  @inlinable
  internal func symmetricDifference(
    _ other: _BTree,
    by strategy: _BTreeMatchingStrategy
  ) -> _BTree {
    var m = _BTreeMerger(first: self, second: other)
    while !m.done {
      m.copyFromFirst(.excludingOtherKey)
      m.copyFromSecond(.excludingOtherKey)
      switch strategy {
      case .groupingMatches:
        m.skipCommonElements()
      case .countingMatches:
        m.skipMatchingNumberOfCommonElements()
      @unknown default:
        fatalError("unhandled unknown case")
      }
    }
    m.appendFirst()
    m.appendSecond()
    return m.finish()
  }

  /// Return a tree with those elements of `other` whose keys are also included
  /// in `self`.
  ///
  /// - Parameter other: Any tree with the same order as `self`.
  ///
  /// - Parameter strategy:
  ///      When `.groupingMatches`, all elements in `other` are included that
  ///      have matching keys in `self`, regardless of multiplicities.
  ///
  ///      When `.countingMatches`, for each key, only as many matching elements
  ///      from `other` are kept as the minimum of the key's multiplicities in
  ///      the two trees.
  ///
  /// - Returns: A tree combining elements of `self` and `other` except those
  ///   whose keys can be matched in both trees.
  ///
  /// - Note:
  ///      The elements of the two input trees may interleave and overlap in any
  ///      combination. However, if there are long runs of non-interleaved
  ///      elements, parts of the input trees will be entirely skipped instead
  ///      of elementwise processing. This may drastically improve performance.
  ///
  ///      This function also detects shared subtrees between the two trees,
  ///      and links them directly into the result when possible.
  ///      (Keys that appear in both trees otherwise require individual
  ///      processing.)
  ///
  /// - Requires: `self.order == other.order`
  ///
  /// - Complexity:
  ///    - O(min(*n*, *m*)) in general, where *n* is the
  ///      length of the tree and *m* is the length of the other tree.
  ///    - O(log(*n* + *m*) if there are only a constant
  ///      amount of interleaving element runs, where *n* is the
  ///      length of the tree and *m* is the length of the other tree.
  @inlinable
  internal func intersection(
    _ other: _BTree,
    by strategy: _BTreeMatchingStrategy
  ) -> _BTree {
    var m = _BTreeMerger(first: self, second: other)
    while !m.done {
      m.skipFromFirst(.excludingOtherKey)
      m.skipFromSecond(.excludingOtherKey)
      switch strategy {
      case .groupingMatches:
        m.copyCommonElementsFromSecond()
      case .countingMatches:
        m.copyMatchingNumberOfCommonElementsFromSecond()
      @unknown default:
        fatalError("unhandled unknown case")
      }
    }
    return m.finish()
  }

  /// Return a tree that contains all elements in `self` whose key is not in the
  /// supplied sorted sequence.
  ///
  /// - Note:
  ///      The keys of `self` may interleave and overlap with `sortedKeys` in
  ///      any combination. However, if there are long runs of non-interleaved
  ///      keys, parts of `self` will be entirely skipped instead of elementwise
  ///      processing. This may drastically improve performance.
  ///
  /// - Requires: `sortedKeys` is sorted in ascending order.
  /// - Complexity: O(*n* + *m*), where *n* is the length of the tree and *m* is
  ///   the length of `sortedKeys`.
  @inlinable
  internal func subtracting<S: Sequence>(
    sortedKeys: S,
    by strategy: _BTreeMatchingStrategy
  ) -> _BTree where S.Element == Key {
    if self.isEmpty { return self }

    var b = _BTreeBuilder<Key, Value>(order: self.order)
    var lastKey: Key? = nil
    var path = _BTreeStrongPath(startOf: self.root)
    outer: for key in sortedKeys {
      precondition(lastKey == nil ||  lastKey! <= key)
      lastKey = key
      while path.key < key {
        b.append(path.nextPart(until: .excluding(key)))
        if path.isAtEnd { break outer }
      }
      switch strategy {
      case .groupingMatches:
        while path.key == key {
          path.nextPart(until: .including(key))
          if path.isAtEnd { break outer }
        }
      case .countingMatches:
        if path.key == key {
          path.moveForward()
          if path.isAtEnd { break outer }
        }
      @unknown default:
        fatalError("unhandled unknown case")
      }
    }
    if !path.isAtEnd {
      b.append(path.element)
      b.appendWithoutCloning(path.suffix().root)
    }
    return _BTree(b.finish())
  }

  /// Remove all elements that return true for predicate.
  ///
  /// - Complexity: O(*n*), where *n* is the length of the tree.
  @inlinable
  internal mutating func removeAll(where predicate: (Element) -> Bool) {
    if self.isEmpty { return }

    var b = _BTreeBuilder<Key, Value>(order: self.order)
    forEach { element -> Void in
      if !predicate(element) {
        b.append(element)
      }
    }
    root = b.finish()
  }

  /// Remove all elements that return true for predicate.
  ///
  /// - Complexity: O(*n*), where *n* is the length of the tree.
  @inlinable
  internal mutating func removeAll(where predicate: (Key) -> Bool) {
    if self.isEmpty { return }

    var b = _BTreeBuilder<Key, Value>(order: self.order)
    forEach { element -> Void in
      if !predicate(element.key) {
        b.append(element)
      }
    }
    root = b.finish()
  }

  /// Return a tree that contains all elements in `self` whose key is in the
  /// supplied sorted sequence.
  ///
  /// - Note:
  ///      The keys of `self` may interleave and overlap with `sortedKeys` in
  ///      any combination. However, if there are long runs of non-interleaved
  ///      keys, parts of `self` will be entirely skipped instead of elementwise
  ///      processing. This may drastically improve performance.
  ///
  /// - Requires: `sortedKeys` is sorted in ascending order.
  /// - Complexity: O(*n* + *m*), where *n* is the length of the tree and *m* is
  ///   the length of `sortedKeys`.
  @inlinable
  internal func intersection<S: Sequence>(
    sortedKeys: S,
    by strategy: _BTreeMatchingStrategy
  ) -> _BTree where S.Element == Key {
    if self.isEmpty { return self }

    var b = _BTreeBuilder<Key, Value>(order: self.order)
    var lastKey: Key? = nil
    var path = _BTreeStrongPath(startOf: self.root)
    outer: for key in sortedKeys {
      precondition(lastKey == nil || lastKey! <= key)
      lastKey = key
      while path.key < key {
        path.nextPart(until: .excluding(key))
        if path.isAtEnd { break outer }
      }
      switch strategy {
      case .groupingMatches:
        while path.key == key {
          b.append(path.nextPart(until: .including(key)))
          if path.isAtEnd { break outer }
        }
      case .countingMatches:
        if path.key == key {
          b.append(path.element)
          path.moveForward()
          if path.isAtEnd { break outer }
        }
      @unknown default:
        fatalError("unhandled unknown case")
      }
    }
    return _BTree(b.finish())
  }
}

@usableFromInline
enum _BTreeLimit<Key: Comparable> {
  case including(Key)
  case excluding(Key)

  @inlinable
  func match(_ key: Key) -> Bool {
    switch self {
    case .including(let limit):
      return key <= limit
    case .excluding(let limit):
      return key < limit
    @unknown default:
      fatalError("unhandled unknown case")
    }
  }
}

@usableFromInline
enum _BTreeRelativeLimit {
  case includingOtherKey
  case excludingOtherKey

  @inlinable
  func with<Key: Comparable>(_ key: Key) -> _BTreeLimit<Key> {
    switch self {
    case .includingOtherKey:
      return .including(key)
    case .excludingOtherKey:
      return .excluding(key)
    @unknown default:
      fatalError("unhandled unknown case")
    }
  }
}

/// An abstraction for elementwise/subtreewise merging some of the elements from
/// two trees into a new third tree.
///
/// Merging starts at the beginning of each tree, then proceeds in order from
/// smaller to larger keys. At each step you can decide which tree to merge
/// elements/subtrees from next, until we reach the end of one of the trees.
@usableFromInline
@_fixed_layout
internal struct _BTreeMerger<Key: Comparable, Value> {
  @usableFromInline
  typealias Limit = _BTreeLimit<Key>
  @usableFromInline
  typealias Node = _BTreeNode<Key, Value>

  @usableFromInline
  internal var a: _BTreeStrongPath<Key, Value>
  @usableFromInline
  internal var b: _BTreeStrongPath<Key, Value>
  @usableFromInline
  internal var builder: _BTreeBuilder<Key, Value>

  /// This flag is set to `true` when we've reached the end of one of the trees.
  /// When this flag is set, you may further skips and copies will do nothing.
  /// You may call `appendFirst` and/or `appendSecond` to append the remaining
  /// parts of whichever tree has elements left, or you may call `finish` to
  /// stop merging.
  @usableFromInline
  internal var done: Bool

  /// Construct a new merger starting at the starts of the specified two trees.
  @inlinable
  init(first: _BTree<Key, Value>, second: _BTree<Key, Value>) {
    precondition(first.order == second.order)
    self.a = _BTreeStrongPath(startOf: first.root)
    self.b = _BTreeStrongPath(startOf: second.root)
    self.builder = _BTreeBuilder(
      order: first.order,
      keysPerNode: first.root.maxKeys)
    self.done = first.isEmpty || second.isEmpty
  }

  /// Stop merging and return the merged result.
  @inlinable
  mutating func finish() -> _BTree<Key, Value> {
    return _BTree(builder.finish())
  }

  /// Append the rest of the first tree to the end of the result tree, jump to
  /// the end of the first tree, and set `done` to true.
  ///
  /// You may call this method even when `done` has been set to true by an
  /// earlier operation. It does nothing if the merger has already reached the
  /// end of the first tree.
  ///
  /// - Complexity: O(log *n*), where *n* is the length of the first tree.
  @inlinable
  mutating func appendFirst() {
    if !a.isAtEnd {
      builder.append(a.element)
      builder.append(a.suffix().root)
      a.moveToEnd()
      done = true
    }
  }

  /// Append the rest of the second tree to the end of the result tree, jump to
  /// the end of the second tree, and set `done` to true.
  ///
  /// You may call this method even when `done` has been set to true by an
  /// earlier operation. It does nothing if the merger has already reached the
  /// end of the second tree.
  ///
  /// - Complexity: O(log *n*), where *n* is the length of the second tree.
  @inlinable
  mutating func appendSecond() {
    if !b.isAtEnd {
      builder.append(b.element)
      builder.append(b.suffix().root)
      b.moveToEnd()
      done = true
    }
  }

  /// Copy elements from the first tree (starting at the current position) that
  /// are less than (or, when `limit` is `.includingOtherKey`, less than or
  /// equal to) the key in the second tree at its the current position.
  ///
  /// This method will link entire subtrees to the result whenever possible,
  /// which can considerably speed up the operation.
  ///
  /// This method does nothing if `done` has been set to `true` by an earlier
  /// operation. It sets `done` to true if it reaches the end of the first tree.
  ///
  /// - Complexity: O(*n*) where *n* is the number of elements copied.
  @inlinable
  mutating func copyFromFirst(_ limit: _BTreeRelativeLimit) {
    if !b.isAtEnd {
      copyFromFirst(limit.with(b.key))
    }
  }

  @inlinable
  mutating func copyFromFirst(_ limit: Limit) {
    while !a.isAtEnd && limit.match(a.key) {
        builder.append(a.nextPart(until: limit))
    }
    if a.isAtEnd {
      done = true
    }
  }

  /// Copy elements from the second tree (starting at the current position) that
  /// are less than (or, when `limit` is `.includingOtherKey`, less than or
  /// equal to) the key in the first tree at its the current position.
  ///
  /// This method will link entire subtrees to the result whenever possible,
  /// which can considerably speed up the operation.
  ///
  /// This method does nothing if `done` has been set to `true` by an earlier
  /// operation. It sets `done` to true if it reaches the end of the second
  /// tree.
  ///
  /// - Complexity: O(*n*) where *n* is the number of elements copied.
  @inlinable
  mutating func copyFromSecond(_ limit: _BTreeRelativeLimit) {
    if !a.isAtEnd {
      copyFromSecond(limit.with(a.key))
    }
  }

  @inlinable
  mutating func copyFromSecond(_ limit: Limit) {
    while !b.isAtEnd && limit.match(b.key) {
        builder.append(b.nextPart(until: limit))
    }
    if b.isAtEnd {
      done = true
    }
  }

  /// Skip elements from the first tree (starting at the current position) that
  /// are less than (or, when `limit` is `.includingOtherKey`, less than or
  /// equal to) the key in the second tree at its the current position.
  ///
  /// This method will jump over entire subtrees to the result whenever
  /// possible, which can considerably speed up the operation.
  ///
  /// This method does nothing if `done` has been set to `true` by an earlier
  /// operation. It sets `done` to true if it reaches the end of the first tree.
  ///
  /// - Complexity: O(*n*) where *n* is the number of elements skipped.
  @inlinable
  mutating func skipFromFirst(_ limit: _BTreeRelativeLimit) {
    if !b.isAtEnd {
      skipFromFirst(limit.with(b.key))
    }
  }

  @inlinable
  mutating func skipFromFirst(_ limit: Limit) {
    while !a.isAtEnd && limit.match(a.key) {
        a.nextPart(until: limit)
    }
    if a.isAtEnd {
      done = true
    }
  }

  /// Skip elements from the second tree (starting at the current position) that
  /// are less than (or, when `limit`  is `.includingOtherKey`, less than or
  /// equal to) the key in the first tree at its the current position.
  ///
  /// This method will jump over entire subtrees to the result whenever
  /// possible, which can considerably speed up the operation.
  ///
  /// This method does nothing if `done` has been set to `true` by an earlier
  /// operation. It sets `done` to true if it reaches the end of the second
  /// tree.
  ///
  /// - Complexity: O(*n*) where *n* is the number of elements skipped.
  @inlinable
  mutating func skipFromSecond(_ limit: _BTreeRelativeLimit) {
    if !a.isAtEnd {
      skipFromSecond(limit.with(a.key))
    }
  }

  @inlinable
  mutating func skipFromSecond(_ limit: Limit) {
    while !b.isAtEnd && limit.match(b.key) {
        b.nextPart(until: limit)
    }
    if b.isAtEnd {
      done = true
    }
  }

  /// Take the longest possible sequence of elements that share the same key in
  /// both trees; ignore elements from the first tree, but append elements from
  /// the second tree to the end of the result tree.
  ///
  /// This method does not care how many duplicate keys it finds for each key.
  /// For example, with `first = [0, 0, 1, 2, 2, 5, 6, 7]`,
  /// `second = [0, 1, 1, 1, 2, 2, 6, 8]`, it appends `[0, 1, 1, 1, 2, 2]`
  /// to the result, and leaves the first tree at `[5, 6, 7]` and the second at
  /// `[6, 8]`.
  ///
  /// This method recognizes nodes that are shared between the two trees, and
  /// links them to the result in one step. This can considerably speed up the
  /// operation.
  ///
  /// - Complexity: O(*n*) where *n* is the number of elements processed.
  @inlinable
  mutating func copyCommonElementsFromSecond() {
    while !done && a.key == b.key {
      if a.node === b.node && a.node.isLeaf && a.slot == 0 && b.slot == 0 {
        /// We're at the first element of a shared subtree. Find the ancestor at
        /// which the shared subtree starts, and append it in a single step.
        ///
        /// It might happen that a shared node begins with a key that we've
        /// already fully processed in one of the trees. In this case, we cannot
        /// skip elementwise processing, since the trees are at different
        /// offsets in the shared subtree. The slot & leaf checks above & below
        /// ensure that this isn't the case.
        var key: Key
        var common: Node
        repeat {
          key = a.node.last!.0
          common = a.node
          a.ascendOneLevel()
          b.ascendOneLevel()
        } while !a.isAtEnd
          && !b.isAtEnd && a.node === b.node && a.slot == 0 && b.slot == 0
        builder.append(common)
        if !a.isAtEnd {
          a.ascendToKey()
          skipFromFirst(.including(key))
        }
        if !b.isAtEnd {
          b.ascendToKey()
          copyFromSecond(.including(key))
        }
        if a.isAtEnd || b.isAtEnd {
          done = true
        }
      } else {
        // Process the next run of equal keys in both trees, skipping them in
        // `first`, but copying them from `second`.
        // Note that we cannot leave matching elements in either tree, even if
        // we reach the end of the other.
        let key = a.key
        skipFromFirst(.including(key))
        copyFromSecond(.including(key))
      }
    }
  }

  @inlinable
  mutating func copyMatchingNumberOfCommonElementsFromSecond() {
    while !done && a.key == b.key {
      if a.node === b.node && a.node.isLeaf && a.slot == 0 && b.slot == 0 {
        /// We're at the first element of a shared subtree. Find the ancestor at
        /// which the shared subtree starts, and append it in a single step.
        ///
        /// It might happen that a shared node begins with a key that we've
        /// already fully processed in one of the trees. In this case, we cannot
        /// skip elementwise processing, since the trees are at different
        /// offsets in the shared subtree. The slot & leaf checks above & below
        /// ensure that this isn't the case.
        var common: Node
        repeat {
          common = a.node
          a.ascendOneLevel()
          b.ascendOneLevel()
        } while !a.isAtEnd
          && !b.isAtEnd
          && a.node === b.node
          && a.slot == 0
          && b.slot == 0
        builder.append(common)
        if !a.isAtEnd { a.ascendToKey() }
        if !b.isAtEnd { b.ascendToKey() }
        if a.isAtEnd || b.isAtEnd {
          done = true
        }
      } else {
        // Copy one matching element from the second tree, then step forward.
        // TODO: Count the number of matching elements in a and link entire
        // subtrees from b into the result when possible.
        builder.append(b.element)
        a.moveForward()
        b.moveForward()
        done = a.isAtEnd || b.isAtEnd
      }
    }
  }

  /// Ignore and jump over the longest possible sequence of elements that share
  /// the same key in both trees, starting at the current positions.
  ///
  /// This method does not care how many duplicate keys it finds for each key.
  /// For example, with `first = [0, 0, 1, 2, 2, 5, 6, 7]`,
  /// `second = [0, 1, 1, 1, 2, 2, 6, 8]`, it skips to `[5, 6, 7]` in the first
  /// tree, and `[6, 8]` in the second.
  ///
  /// This method recognizes nodes that are shared between the two trees, and
  /// jumps over them in one step. This can considerably speed up the operation.
  ///
  /// - Complexity: O(*n*) where *n* is the number of elements processed.
  @inlinable
  mutating func skipCommonElements() {
    while !done && a.key == b.key {
      if a.node === b.node {
        /// We're inside a shared subtree. Find the ancestor at which the shared
        /// subtree starts, and append it in a single step.
        ///
        /// This variant doesn't care about where we're in the shared subtree.
        /// It assumes that if we ignore one set of common keys, we're ignoring
        /// all.
        var key: Key
        repeat {
          key = a.node.last!.0
          assert(a.slot == b.slot)
          a.ascendOneLevel()
          b.ascendOneLevel()
          if a.isAtEnd || b.isAtEnd {
            done = true
          }
        } while !done && a.node === b.node
        if !a.isAtEnd {
          a.ascendToKey()
          skipFromFirst(.including(key))
        }
        if !b.isAtEnd {
          b.ascendToKey()
          skipFromSecond(.including(key))
        }
      } else {
        // Process the next run of equal keys in both trees, skipping them in
        // both trees.
        // Note that we cannot leave matching elements in either tree, even if
        // we reach the end of the other.
        let key = a.key
        skipFromFirst(.including(key))
        skipFromSecond(.including(key))
      }
    }
  }

  @inlinable
  mutating func skipMatchingNumberOfCommonElements() {
    while !done && a.key == b.key {
      if a.node === b.node && a.node.isLeaf && a.slot == b.slot {
        /// We're at the first element of a shared subtree. Find the ancestor at
        /// which the shared subtree starts, and append it in a single step.
        ///
        /// It might happen that a shared node begins with a key that we've
        /// already fully processed in one of the trees.
        /// In this case, we cannot skip elementwise processing, since the trees
        /// are at different offsets in the shared subtree. The slot & leaf
        /// checks above & below ensure that this isn't the case.
        repeat {
          a.ascendOneLevel()
          b.ascendOneLevel()
          if a.isAtEnd || b.isAtEnd {
            done = true
          }
        } while !done && a.node === b.node && a.slot == b.slot
        if !a.isAtEnd { a.ascendToKey() }
        if !b.isAtEnd { b.ascendToKey() }
      } else {
        // Skip one matching element from both trees.
        a.moveForward()
        b.moveForward()
        done = a.isAtEnd || b.isAtEnd
      }
    }
  }
}

@usableFromInline
internal enum _BTreePart<Key: Comparable, Value> {
  case element((key: Key, value: Value))
  case node(_BTreeNode<Key, Value>)
  case nodeRange(_BTreeNode<Key, Value>, CountableRange<Int>)
}

extension _BTreePart {
  @inlinable
  var count: Int {
    switch self {
    case .element:
      return 1
    case .node(let node):
      return node.count
    case .nodeRange(let parent, let range):
      var count = range.count
      if !parent.isLeaf {
        for i in range.lowerBound ... range.upperBound {
          count += parent.children[i].count
        }
      }
      return count
    @unknown default:
      fatalError("unhandled unknown case")
    }
  }
}

extension _BTreeBuilder {
  @inlinable
  mutating func append(_ part: _BTreePart<Key, Value>) {
    switch part {
    case .element(let element):
      self.append(element)
    case .node(let node):
      self.append(node)
    case .nodeRange(let node, let range):
      self.appendWithoutCloning(Node(node: node, slotRange: range))
    @unknown default:
      fatalError("unhandled unknown case")
    }
  }
}

extension _BTreeStrongPath {
  @usableFromInline
  typealias Limit = _BTreeLimit<Key>

  /// The parent of `node` and the slot of `node` in its parent, or `nil` if
  /// `node` is the root node.
  @inlinable
  internal var parent: (Node, Int)? {
    guard !_path.isEmpty else { return nil }
    return (_path.last!, _slots.last!)
  }

  /// The key following the `node` at the same slot in its parent, or `nil` if
  /// there is no such key.
  @inlinable
  internal var parentKey: Key? {
    guard let parent = self.parent else { return nil }
    guard parent.1 < parent.0.elements.count else { return nil }
    return parent.0.elements[parent.1].0
  }

  /// Move sideways `n` slots to the right, skipping over subtrees along the
  /// way.
  @inlinable
  mutating func skipForward(_ n: Int) {
    if !node.isLeaf {
      for i in 0 ..< n {
        let s = slot! + i
        offset += node.children[s + 1].count
      }
    }
    offset += n
    slot! += n
    if offset != count {
      ascendToKey()
    }
  }

  /// Remove the deepest path component, leaving the path at the element
  /// following the node that was previously focused, or the spot after all
  /// elements if the node was the rightmost child.
  @inlinable
  mutating func ascendOneLevel() {
    if length == 1 {
      offset = count
      slot = node.elements.count
      return
    }
    popFromSlots()
    popFromPath()
  }

  /// If this path got to a slot at the end of a node but it hasn't reached the
  /// end of the tree yet, ascend to the ancestor that holds the key
  /// corresponding to the current offset.
  @inlinable
  mutating func ascendToKey() {
    assert(!isAtEnd)
    while slot == node.elements.count {
      slot = nil
      popFromPath()
    }
  }

  /// Return the next part in this tree that consists of elements less than
  /// `key`. If `inclusive` is true, also include elements matching `key`.
  /// The part returned is either a single element, or a range of elements in a
  /// node, including their associated subtrees.
  ///
  /// - Requires: The current position is not at the end of the tree, and the
  ///   current key is matching the condition above.
  /// - Complexity: O(log *n*) where *n* is the number of elements in the
  ///   returned part.
  @inlinable
  @discardableResult
  mutating func nextPart(until limit: Limit) -> _BTreePart<Key, Value> {
    assert(!isAtEnd && limit.match(self.key))

    // Find furthest ancestor whose entire leftmost subtree is guaranteed to
    // consist of matching elements.
    assert(!isAtEnd)
    var includeLeftmostSubtree = false
    if slot == 0 && node.isLeaf {
      while slot == 0, let pk = parentKey, limit.match(pk) {
          popFromSlots()
          popFromPath()
          includeLeftmostSubtree = true
      }
    }
    if !includeLeftmostSubtree && !node.isLeaf {
      defer { moveForward() }
      return .element(self.element)
    }

    // Find range of matching elements in `node`.
    assert(limit.match(self.key))
    let startSlot = slot!
    var endSlot = startSlot + 1
    while endSlot < node.elements.count
      && limit.match(node.elements[endSlot].0) {
      endSlot += 1
    }

    // See if we can include the subtree following the last matching element.
    // This is a log(n) check but it's worth it.
    let includeRightmostSubtree = node.isLeaf
      || limit.match(node.children[endSlot].last!.0)
    if includeRightmostSubtree {
      defer { skipForward(endSlot - startSlot) }
      return .nodeRange(node, startSlot ..< endSlot)
    }
    // If the last subtree has non-matching elements, leave off `endSlot - 1`
    // from the returned range.
    if endSlot == startSlot + 1 {
      let n = node.children[slot!]
      return .node(n)
    }
    defer { skipForward(endSlot - startSlot - 1) }
    return .nodeRange(node, startSlot ..< endSlot - 1)
  }
}
