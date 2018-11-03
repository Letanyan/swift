//===--- SortedArray.swift ------------------------------------*- swift -*-===//
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

/// A sorted collection of unique comparable elements.
/// `SortedSet` is like `Set` in the standard library, but it always keeps its
/// elements in ascending order. Lookup, insertion and removal of any element
/// has logarithmic complexity.
///
/// `SortedSet` is a struct with copy-on-write value semantics, like Swift's
/// standard collection types. It uses an in-memory b-tree for element storage,
/// whose individual nodes may be shared with other sorted sets. Mutating a set
/// whose storage is (partially or completely) shared requires copying of only
/// O(log(`count`)) elements. (Thus, mutation of shared `SortedSet`s may be
/// cheaper than ordinary `Set`s, which need to copy all elements.)
///
/// Set operations on sorted sets (such as taking the union, intersection or
/// difference) can take as little as O(log(n)) time if the elements in the
/// input sets aren't too interleaved.
@_fixed_layout
public struct SortedSet<Element: Equatable> {
  @_fixed_layout
  public struct Index: Comparable {
    @usableFromInline
    internal var _base: _BTreeIndex<Element, Void>

    @inlinable
    internal init(_ base: _BTreeIndex<Element, Void>) {
      _base = base
    }

    @inlinable
    public static func < (lhs: Index, rhs: Index) -> Bool {
      return lhs._base < rhs._base
    }

    @inlinable
    public static func == (lhs: Index, rhs: Index) -> Bool {
      return lhs._base == rhs._base
    }
  }

  @_fixed_layout
  public struct Iterator: IteratorProtocol {
    @usableFromInline
    internal var _base: _BTreeKeyIterator<Element>

    @inlinable
    internal init(_ base: _BTreeKeyIterator<Element>) {
      _base = base
    }

    /// Advance to the next element and return it, or return `nil` if no next
    /// element exists.
    ///
    /// - Complexity: Amortized O(1)
    @inlinable
    public mutating func next() -> Element? {
      return _base.next()
    }
  }

  @usableFromInline
  internal typealias Tree = _BTree<Element, Void>

  /// The b-tree that serves as storage.
  @usableFromInline
  internal var tree: Tree // fileprivate(set)

  @inlinable
  internal init(_ tree: Tree) {
    self.tree = tree
  }
}

extension SortedSet {
  /// Create a set from a finite sequence of items. The sequence need not be
  /// sorted. If the sequence contains duplicate items, only the last instance
  /// will be kept in the set.
  ///
  /// - Complexity: O(*n* * log(*n*)), where *n* is the number of items in the
  /// sequence.
  @inlinable
  public init<S: Sequence>(
    unsortedElements elements: S,
    areInIncreasingOrder: @escaping (Element, Element) -> Bool
  ) where S.Element == Element {
    let sortedElements = elements.sorted(by: areInIncreasingOrder)
      .lazy
      .map { (key: $0, value: ()) }
    self.init(Tree(
      sortedElements: sortedElements, dropDuplicates: true,
      areInIncreasingOrder: areInIncreasingOrder))
  }

  /// Create a set from a sorted finite sequence of items. If the sequence
  /// contains duplicate items, only the last instance will be kept in the set.
  ///
  /// - Complexity: O(*n*), where *n* is the number of items in the sequence.
  @inlinable
  public init<S: Sequence>(
    sortedElements elements: S,
    areInIncreasingOrder: @escaping (Element, Element) -> Bool
  ) where S.Element == Element {
    self.init(Tree(
      sortedElements: elements.lazy.map { (key: $0, value: ()) },
      dropDuplicates: true, areInIncreasingOrder: areInIncreasingOrder))
  }

  /// Create an empty set.
  @inlinable
  public init(areInIncreasingOrder: @escaping (Element, Element) -> Bool) {
    self.tree = Tree(areInIncreasingOrder: areInIncreasingOrder)
  }
}

extension SortedSet: SetAlgebra where Element: Comparable {
  @inlinable
  public init() {
    tree = Tree(areInIncreasingOrder: <)
  }

  /// Create a sorted set from a finite sequence of items. The sequence
  /// need not be sorted.
  ///
  /// - Complexity: O(*n* * log(*n*)), where *n* is the number of items in the
  ///   sequence.
  public init<S: Sequence>(unsortedElements elements: S)
  where S.Element == Element {
    self.init(unsortedElements: elements, areInIncreasingOrder: <)
  }

  /// Create a sorted set from a sorted finite sequence of items.
  ///
  /// - Complexity: O(*n*), where *n* is the number of items in the sequence.
  public init<S: Sequence>(sortedElements elements: S)
  where S.Element == Element {
    self.init(sortedElements: elements, areInIncreasingOrder: <)
  }
}

extension SortedSet: ExpressibleByArrayLiteral where Element: Comparable {
  public typealias ArrayLiteralElement = Element

  /// Create a set with the specified list of items. If the array literal
  /// contains duplicate items, only the last instance will be kept.
  @inlinable
  public init(arrayLiteral elements: Element...) {
    self.init(unsortedElements: elements)
  }
}

extension SortedSet: SortedInsertableCollection {
  /// A predicate that returns `true` if its first argument should be ordered
  /// before its second argument; otherwise, `false`.
  @inlinable
  public var areInIncreasingOrder: (Element, Element) -> Bool {
    return tree.areInIncreasingOrder
  }

  /// Returns the index of where the given key would be after insertion and
  /// whether a key already exists that is equal to the given key.
  ///
  /// - Returns: `keyAlreadyExists` must be return true if a key that is equal
  ///   to the given key already exists in the set, otherwise return
  ///   false. `location` must return the index where the given key would be
  ///   inserted.
  /// - Complexity: O(log(*n*)), where *n* is the count of the set.
  @inlinable
  public func insertionPoint(
    for key: Key
  ) -> (keyAlreadyExists: Bool, location: Index) {
    if let idx = tree.index(forKey: key) {
      return (true, Index(idx))
    } else {
      return (false, Index(tree.index(forInserting: key)))
    }
  }

  /// Inserts an element into the set. The set must remain sorted
  /// after the new element is inserted.
  ///
  /// - Returns: `inserted` must be false if the element was not inserted into
  ///   the set, otherwise return true. `location` should return the
  ///   index of where the element was inserted or where it would have been
  ///   inserted.
  /// - Complexity: O(log(*n*)), where *n* is the count of the set
  @inlinable
  @discardableResult
  public mutating func insert(
    _ element: Element
  ) -> (inserted: Bool, location: Index) {
    guard let old = tree.insertOrFind((element, ())) else {
      return (true, Index(tree.index(forKey: element)!))
    }
    return (false, Index(tree.index(forKey: old.0)!))
  }
}

extension SortedSet: BidirectionalCollection {
  // public typealias SubSequence = Slice<SortedSet<Element>>

  /// The index of the first element when non-empty. Otherwise the same as
  /// `endIndex`.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public var startIndex: Index {
    return Index(tree.startIndex)
  }

  /// The "past-the-end" element index; the successor of the last valid
  /// subscript argument.
  ///
  /// - Complexity: O(1)
  @inlinable
  public var endIndex: Index {
    return Index(tree.endIndex)
  }

  /// The number of elements in this set.
  @inlinable
  public var count: Int {
    return tree.count
  }

  /// True iff this collection has no elements.
  @inlinable
  public var isEmpty: Bool {
    return count == 0
  }

  /// Returns the element at the given index.
  ///
  /// - Requires: `index` originated from an unmutated copy of this set.
  /// - Complexity: O(1)
  @inlinable
  public subscript(index: Index) -> Element {
    return tree[index._base].0
  }

  /// Return an iterator over all elements in this map, in ascending key order.
  @inlinable
  public func makeIterator() -> Iterator {
    return Iterator(_BTreeKeyIterator(tree.makeIterator()))
  }

  /// Returns the successor of the given index.
  ///
  /// - Requires: `index` is a valid index of this set and it is not equal to
  ///   `endIndex`.
  /// - Complexity: Amortized O(1).
  @inlinable
  public func index(after index: Index) -> Index {
    return Index(tree.index(after: index._base))
  }

  /// Replaces the given index with its successor.
  ///
  /// - Requires: `index` is a valid index of this set and it is not equal to
  ///   `endIndex`.
  /// - Complexity: Amortized O(1).
  @inlinable
  public func formIndex(after index: inout Index) {
    tree.formIndex(after: &index._base)
  }

  /// Returns the predecessor of the given index.
  ///
  /// - Requires: `index` is a valid index of this set and it is not equal to
  ///   `startIndex`.
  /// - Complexity: Amortized O(1).
  @inlinable
  public func index(before index: Index) -> Index {
    return Index(tree.index(before: index._base))
  }

  /// Replaces the given index with its predecessor.
  ///
  /// - Requires: `index` is a valid index of this set and it is not equal to
  ///   `startIndex`.
  /// - Complexity: Amortized O(1).
  @inlinable
  public func formIndex(before index: inout Index) {
    tree.formIndex(before: &index._base)
  }

  /// Returns an index that is at the specified distance from the given index.
  ///
  /// - Requires: `index` must be a valid index of this set.
  ///   If `n` is positive, it must not exceed the distance from `index` to
  ///   `endIndex`.
  ///   If `n` is negative, it must not be less than the distance from `index`
  ///   to `startIndex`.
  /// - Complexity: O(log(*count*)) where *count* is the number of elements in
  ///   the set.
  @inlinable
  public func index(_ i: Index, offsetBy n: Int) -> Index {
    return Index(tree.index(i._base, offsetBy: n))
  }

  /// Offsets the given index by the specified distance.
  ///
  /// - Requires: `index` must be a valid index of this set.
  ///   If `n` is positive, it must not exceed the distance from `index` to
  ///   `endIndex`.
  ///   If `n` is negative, it must not be less than the distance from `index`
  ///   to `startIndex`.
  /// - Complexity: O(log(*count*)) where *count* is the number of elements in
  ///   the set.
  public func formIndex(_ i: inout Index, offsetBy n: Int) {
    tree.formIndex(&i._base, offsetBy: n)
  }

  /// Returns an index that is at the specified distance from the given index,
  /// unless that distance is beyond a given limiting index.
  ///
  /// - Requires: `index` and `limit` must be valid indices in this set. The
  ///   operation must not advance the index beyond `endIndex` or before
  ///   `startIndex`.
  /// - Complexity: O(log(*count*)) where *count* is the number of elements in
  ///   the set.
  @inlinable
  public func index(
    _ i: Index,
    offsetBy n: Int,
    limitedBy limit: Index
  ) -> Index? {
    guard let idx = tree.index(
      i._base, offsetBy: n, limitedBy: limit._base) else {
        return nil
    }
    return Index(idx)
  }

  /// Offsets the given index by the specified distance, or so that it equals
  /// the given limiting index.
  ///
  /// - Requires: `index` and `limit` must be valid indices in this set. The
  ///   operation must not advance the index beyond `endIndex` or before
  ///   `startIndex`.
  /// - Complexity: O(log(*count*)) where *count* is the number of elements in
  ///   the set.
  @inlinable
  @discardableResult
  public func formIndex(
    _ i: inout Index,
    offsetBy n: Int,
    limitedBy limit: Index
  ) -> Bool {
    return tree.formIndex(&i._base, offsetBy: n, limitedBy: limit._base)
  }

  /// Returns the distance between two indices.
  ///
  /// - Requires: `start` and `end` must be valid indices in this set.
  /// - Complexity: O(1)
  @inlinable
  public func distance(from start: Index, to end: Index) -> Int {
    return tree.distance(from: start._base, to: end._base)
  }
}

extension SortedSet {
  /// Returns the index at offset.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public func index(atOffset offset: Int) -> Index {
    return Index(tree.index(ofOffset: offset))
  }

  /// Returns the offset of index
  ///
  /// - Requires: `offset >= 0 && offset < count`
  /// - Complexity: O(log(`count`))
  @inlinable
  public func offset(of index: Index) -> Int {
    return tree.offset(of: index._base)
  }

  /// Return the offset of `member`, if it is an element of this set. Otherwise,
  /// return `nil`.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public func offset(of member: Element) -> Int? {
    return tree.offset(forKey: member)
  }

  /// Returns the element at `offset` from the start of the set.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public subscript(offset offset: Int) -> Element {
    return tree.element(atOffset: offset).0
  }

  /// Returns the subset containing elements in the specified range of offsets
  /// from the start of the set.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public subscript(
    offset offsetRange: Range<Int>
  ) -> Slice<SortedSet<Element>> {
    let start = index(atOffset: offsetRange.lowerBound)
    let end = index(atOffset: offsetRange.upperBound)
    return Slice(base: self, bounds: start..<end)
  }
}

extension SortedSet {
  /// Call `body` on each element in `self` in ascending order.
  @inlinable
  public func forEach(_ body: (Element) throws -> Void) rethrows {
    return try tree.forEach { try body($0.0) }
  }

  /// Return an `Array` containing the results of mapping transform over `self`.
  @inlinable
  public func map<T>(_ transform: (Element) throws -> T) rethrows -> [T] {
    return try tree.map { try transform($0.0) }
  }

  /// Return an `Array` containing the concatenated results of mapping
  /// `transform` over `self`.
  @inlinable
  public func flatMap<S : Sequence>(
    _ transform: (Element) throws -> S
  ) rethrows -> [S.Element] {
    return try tree.flatMap { try transform($0.0) }
  }

  /// Return an `Array` containing the non-`nil` results of mapping `transform`
  /// over `self`.
  @inlinable
  public func flatMap<T>(_ transform: (Element) throws -> T?) rethrows -> [T] {
    return try tree.compactMap { try transform($0.0) }
  }

  /// Return an `Array` containing the elements of `self`, in ascending order,
  /// that satisfy the predicate `includeElement`.
  @inlinable
  public func filter(
    _ includeElement: (Element) throws -> Bool
  ) rethrows -> [Element] {
    var result: [Element] = []
    try tree.forEach { e -> Void in
      if try includeElement(e.0) {
        result.append(e.0)
      }
    }
    return result
  }

  /// Return the result of repeatedly calling `combine` with an accumulated
  /// value initialized to `initial` and each element of `self`, in turn.
  /// I.e., return `combine(combine(...combine(combine(initial, self[0]), self[1]),...self[count-2]), self[count-1])`.
  @inlinable
  public func reduce<T>(
    _ initialResult: T,
    _ nextPartialResult: (T, Element) throws -> T
  ) rethrows -> T {
    return try tree.reduce(initialResult) { try nextPartialResult($0, $1.0) }
  }
}

extension SortedSet {
  /// Return the smallest element in the set, or `nil` if the set is empty.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public var first: Element? { return tree.first?.0 }

  /// Return the largest element in the set, or `nil` if the set is empty.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public var last: Element? { return tree.last?.0 }

  /// Return the smallest element in the set, or `nil` if the set is empty.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public func min() -> Element? { return first }

  /// Return the largest element in the set, or `nil` if the set is empty.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public func max() -> Element? { return last }
}

extension SortedSet {
  /// Return true if the set contains `element`.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public func contains(_ element: Element) -> Bool {
    return tree.value(of: element) != nil
  }

  /// Returns the index of a given member, or `nil` if the member is not present
  /// in the set.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public func firstIndex(of member: Element) -> Index? {
    guard let idx = tree.index(forKey: member) else {
      return nil
    }
    return Index(idx)
  }

  /// Returns the index of the last instance of a given member, or `nil` if the
  /// member is not present in the sorted array.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public func lastIndex(of member: Element) -> Index? {
    guard let index = tree.index(forKey: member, choosing: .last) else {
      return nil
    }
    return Index(index)
  }
}

extension SortedSet {
  /// Insert a member into the set if it is not already present.
  ///
  /// - Returns: `(true, newMember)` if `newMember` was not contained in the
  ///   set. If an element equal to `newMember` was already contained in the
  ///   set, the method returns `(false, oldMember)`, where `oldMember` is the
  ///   element that was equal to `newMember`. In some cases, `oldMember` may be
  ///   distinguishable from `newMember` by identity comparison or some other
  ///   means.
  /// - Complexity: O(log(`count`))
  @inlinable
  @discardableResult
  public mutating func insert(
    _ newMember: Element
  ) -> (inserted: Bool, memberAfterInsert: Element) {
    guard let old = tree.insertOrFind((newMember, ())) else {
      return (true, newMember)
    }
    return (false, old.0)
  }

  /// Inserts the given element into the set unconditionally.
  ///
  /// If an element equal to `newMember` is already contained in the set,
  /// `newMember` replaces the existing element.
  ///
  /// - Parameter newMember: An element to insert into the set.
  /// - Returns: The element equal to `newMember` that was originally in the
  ///   set, if exists; otherwise, `nil`. In some cases, the returned element
  ///   may be distinguishable from `newMember` by identity comparison or some
  ///   other means.
  @inlinable
  @discardableResult
  public mutating func update(with newMember: Element) -> Element? {
    return tree.insertOrReplace((newMember, ()))?.0
  }
}

extension SortedSet {
  /// Removes and returns the first key-value pair of the dictionary if the
  /// dictionary isn't empty.
  ///
  /// - Returns: The first key-value pair of the dictionary if the dictionary
  ///   is not empty; otherwise, `nil`.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public mutating func popFirst() -> Element? {
    guard !isEmpty else { return nil }
    return remove(at: startIndex)
  }

  /// Remove and return the largest member in this set, or return `nil` if the
  /// set is empty.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  @discardableResult
  public mutating func popLast() -> Element? {
    return tree.popLast()?.0
  }

  /// Remove the member referenced by the given index.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  @discardableResult
  public mutating func remove(at index: Index) -> Element {
    return tree.remove(at: index._base).0
  }

  /// Remove the member at the given offset.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  @discardableResult
  public mutating func remove(atOffset offset: Int) -> Element {
    return tree.remove(atOffset: offset).0
  }

  /// Remove all elements in the specified offset range.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public mutating func remove(atOffset offset: Range<Int>) {
    precondition(offset.lowerBound >= 0 && offset.upperBound <= count)
    tree.withCursor(atOffset: offset.lowerBound) { cursor in
      cursor.remove(offset.count)
    }
  }

  /// Remove the member from the set and return it if it was present.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  @discardableResult
  public mutating func remove(_ member: Element) -> Element? {
    return tree.remove(member)?.0
  }

  /// Remove and return the smallest member in this set.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  @discardableResult
  public mutating func removeFirst() -> Element {
    return tree.removeFirst().0
  }

  /// Remove the smallest `n` members from this set.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public mutating func removeFirst(_ n: Int) {
    tree.removeFirst(n)
  }

  /// Remove and return the largest member in this set.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  @discardableResult
  public mutating func removeLast() -> Element {
    return tree.removeLast().0
  }

  /// Remove the largest `n` members from this set.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public mutating func removeLast(_ n: Int) {
    tree.removeLast(n)
  }

  /// Remove a subrange from tree
  ///
  /// - Complexity: O(log(`count`) + `n`) where `n` is the length of the range
  @inlinable
  public mutating func removeSubrange(_ range: Range<Index>) {
    tree.removeSubrange(range.lowerBound._base ..< range.upperBound._base)
  }

  /// Remove a subrange from tree
  ///
  /// - Complexity: O(log(`count`) + `n`) where `n` is the length of the range
  @inlinable
  public mutating func removeSubrange<R>(_ range: R)
  where R: RangeExpression, R.Bound == Index {
    removeSubrange(range.relative(to: self))
  }

  /// Remove all elements that return true for predicate.
  ///
  /// - Complexity: O(`count`)
  @inlinable
  public mutating func removeAll(where predicate: (Element) -> Bool) {
    tree.removeAll(where: predicate)
  }

  /// Remove all members from this set.
  @inlinable
  public mutating func removeAll() {
    tree.removeAll()
  }
}

extension SortedSet {
  /// Return an `Array` containing the members of this set, in ascending order.
  ///
  /// `SortedSet` already keeps its elements sorted, so this is equivalent to
  /// `Array(self)`.
  ///
  /// - Complexity: O(`count`)
  @inlinable
  public func sorted() -> [Element] {
    // The set is already sorted.
    return Array(self)
  }
}

extension SortedSet: Equatable {
  /// Return `true` iff `self` and `other` contain the same elements.
  ///
  /// This method skips over shared subtrees when possible; this can drastically
  /// improve performance when the two sets are divergent mutations originating
  /// from the same value.
  ///
  /// - Complexity:  O(`count`)
  @inlinable
  public func elementsEqual(_ other: SortedSet<Element>) -> Bool {
    return self.tree.elementsEqual(other.tree, by: { $0.0 == $1.0 })
  }

  /// Returns `true` iff `a` contains the same elements as `b`.
  ///
  /// This function skips over shared subtrees when possible; this can
  /// drastically improve performance when the two sets are divergent mutations
  /// originating from the same value.
  ///
  /// - Complexity: O(`count`)
  @inlinable
  public static func ==(a: SortedSet<Element>, b: SortedSet<Element>) -> Bool {
    return a.elementsEqual(b)
  }

  /// Returns `true` iff no members in this set are also included in `other`.
  ///
  /// The elements of the two input sets may be freely interleaved. However, if
  /// there are long runs of non-interleaved elements, parts of the input sets
  /// will be simply linked into the result instead of copying, which can
  /// drastically improve performance.
  ///
  /// - Complexity:
  ///    - O(min(`self.count`, `other.count`)) in general.
  ///    - O(log(`self.count` + `other.count`)) if there are only a constant
  ///      amount of interleaving element runs.
  @inlinable
  public func isDisjoint(with other: SortedSet<Element>) -> Bool {
    return tree.isDisjoint(with: other.tree)
  }

  /// Returns `true` iff all members in this set are also included in `other`.
  ///
  /// The elements of the two input sets may be freely interleaved. However, if
  /// there are long runs of non-interleaved elements, parts of the input sets
  /// will be simply linked into the result instead of copying, which can
  /// drastically improve performance.
  ///
  /// - Complexity:
  ///    - O(min(`self.count`, `other.count`)) in general.
  ///    - O(log(`self.count` + `other.count`)) if there are only a constant
  ///      amount of interleaving element runs.
  @inlinable
  public func isSubset(of other: SortedSet<Element>) -> Bool {
    return tree.isSubset(of: other.tree, by: .groupingMatches)
  }

  /// Returns `true` iff all members in this set are also included in `other`,
  /// but the two sets aren't equal.
  ///
  /// The elements of the two input sets may be freely interleaved.
  /// However, if there are long runs of non-interleaved elements, parts of the
  /// input sets may be skipped instead
  /// of elementwise processing, which can drastically improve performance.
  ///
  /// - Complexity:
  ///    - O(min(`self.count`, `other.count`)) in general.
  ///    - O(log(`self.count` + `other.count`)) if there are only a constant
  ///      amount of interleaving element runs.
  @inlinable
  public func isStrictSubset(of other: SortedSet<Element>) -> Bool {
    return tree.isStrictSubset(of: other.tree, by: .groupingMatches)
  }

  /// Returns `true` iff all members in `other` are also included in this set.
  ///
  /// The elements of the two input sets may be freely interleaved. However, if
  /// there are long runs of non-interleaved elements, parts of the input sets
  /// may be skipped instead of elementwise processing, which can drastically
  /// improve performance.
  ///
  /// - Complexity:
  ///    - O(min(`self.count`, `other.count`)) in general.
  ///    - O(log(`self.count` + `other.count`)) if there are only a constant
  ///      amount of interleaving element runs.
  @inlinable
  public func isSuperset(of other: SortedSet<Element>) -> Bool {
    return tree.isSuperset(of: other.tree, by: .groupingMatches)
  }

  /// Returns `true` iff all members in `other` are also included in this set,
  /// but the two sets aren't equal.
  ///
  /// The elements of the two input sets may be freely interleaved. However, if
  /// there are long runs of non-interleaved elements, parts of the input sets
  /// may be skipped instead of elementwise processing, which can drastically
  /// improve performance.
  ///
  /// - Complexity:
  ///    - O(min(`self.count`, `other.count`)) in general.
  ///    - O(log(`self.count` + `other.count`)) if there are only a constant
  ///      amount of interleaving element runs.
  @inlinable
  public func isStrictSuperset(of other: SortedSet<Element>) -> Bool {
    return tree.isStrictSuperset(of: other.tree, by: .groupingMatches)
  }
}

extension SortedSet {
  /// Return a set containing all members in both this set and `other`.
  ///
  /// The elements of the two input sets may be freely interleaved. However, if
  /// there are long runs of non-interleaved elements, parts of the input sets
  /// will be simply linked into the result instead of copying, which can
  /// drastically improve performance.
  ///
  /// - Complexity:
  ///    - O(min(`self.count`, `other.count`)) in general.
  ///    - O(log(`self.count` + `other.count`)) if there are only a constant
  ///      amount of interleaving element runs.
  @inlinable
  public func union(_ other: SortedSet<Element>) -> SortedSet<Element> {
    return SortedSet(self.tree.union(other.tree, by: .groupingMatches))
  }

  /// Return a set consisting of all members in `other` that are also in this
  /// set.
  ///
  /// The elements of the two input sets may be freely interleaved.
  /// However, if there are long runs of non-interleaved elements, parts of the
  /// input sets will be simply linked into the result instead of copying, which
  /// can drastically improve performance.
  ///
  /// - Complexity:
  ///    - O(min(`self.count`, `other.count`)) in general.
  ///    - O(log(`self.count` + `other.count`)) if there are only a constant
  ///      amount of interleaving element runs.
  @inlinable
  public func intersection(_ other: SortedSet<Element>) -> SortedSet<Element> {
    return SortedSet(self.tree.intersection(other.tree, by: .groupingMatches))
  }

  /// Return a set consisting of members from `self` and `other` that aren't in
  /// both sets at once.
  ///
  /// The elements of the two input sets may be freely interleaved. However, if
  /// there are long runs of non-interleaved elements, parts of the input sets
  /// will be simply linked into the result instead of copying, which can
  /// drastically improve performance.
  ///
  /// - Complexity:
  ///    - O(min(`self.count`, `other.count`)) in general.
  ///    - O(log(`self.count` + `other.count`)) if there are only a constant
  ///      amount of interleaving element runs.
  @inlinable
  public func symmetricDifference(
    _ other: SortedSet<Element>
  ) -> SortedSet<Element> {
    return SortedSet(self.tree.symmetricDifference(
      other.tree, by: .groupingMatches))
  }

  /// Add all members in `other` to this set.
  ///
  /// The elements of the two input sets may be freely interleaved. However, if
  /// there are long runs of non-interleaved elements, parts of the input sets
  /// will be simply linked into the result instead of copying, which can
  /// drastically improve performance.
  ///
  /// - Complexity:
  ///    - O(min(`self.count`, `other.count`)) in general.
  ///    - O(log(`self.count` + `other.count`)) if there are only a constant
  ///      amount of interleaving element runs.
  @inlinable
  public mutating func formUnion(_ other: SortedSet<Element>) {
    self = self.union(other)
  }

  /// Remove all members from this set that are not included in `other`.
  ///
  /// The elements of the two input sets may be freely interleaved. However, if
  /// there are long runs of non-interleaved elements, parts of the input sets
  /// will be simply linked into the result instead of copying, which can
  /// drastically improve performance.
  ///
  /// - Complexity:
  ///    - O(min(`self.count`, `other.count`)) in general.
  ///    - O(log(`self.count` + `other.count`)) if there are only a constant
  ///      amount of interleaving element runs.
  @inlinable
  public mutating func formIntersection(_ other: SortedSet<Element>) {
    self = other.intersection(self)
  }

  /// Replace `self` with a set consisting of members from `self` and `other`
  /// that aren't in both sets at once.
  ///
  /// The elements of the two input sets may be freely interleaved. However, if
  /// there are long runs of non-interleaved elements, parts of the input sets
  /// will be simply linked into the result instead of copying, which can
  /// drastically improve performance.
  ///
  /// - Complexity:
  ///    - O(min(`self.count`, `other.count`)) in general.
  ///    - O(log(`self.count` + `other.count`)) if there are only a constant
  ///      amount of interleaving element runs.
  @inlinable
  public mutating func formSymmetricDifference(_ other: SortedSet<Element>) {
    self = self.symmetricDifference(other)
  }

  /// Return a set containing those members of this set that aren't also
  /// included in `other`.
  ///
  /// The elements of the two input sets may be freely interleaved.
  /// However, if there are long runs of non-interleaved elements, parts of the
  /// input sets will be simply
  /// linked into the result instead of copying, which can drastically improve
  /// performance.
  ///
  /// - Complexity:
  ///    - O(min(`self.count`, `other.count`)) in general.
  ///    - O(log(`self.count` + `other.count`)) if there are only a constant
  ///      amount of interleaving element runs.
  @inlinable
  public func subtracting(_ other: SortedSet) -> SortedSet {
    return SortedSet(self.tree.subtracting(other.tree, by: .groupingMatches))
  }

  /// Remove all members from this set that are also included in `other`.
  ///
  /// The elements of the two input sets may be freely interleaved. However, if
  /// there are long runs of non-interleaved elements, parts of the input sets
  /// will be simply linked into the result instead of copying,  which can
  /// drastically improve performance.
  ///
  /// - Complexity:
  ///    - O(min(`self.count`, `other.count`)) in general.
  ///    - O(log(`self.count` + `other.count`)) if there are only a constant
  ///      amount of interleaving element runs.
  @inlinable
  public mutating func subtract(_ other: SortedSet) {
    self = self.subtracting(other)
  }
}

extension SortedSet: Hashable where Key: Hashable {
  @inlinable
  public func hash(into hasher: inout Hasher) {
    for item in self {
      hasher.combine(item)
    }
  }
}

extension SortedSet: CustomReflectable {
  /// A mirror that reflects the sorted array.
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self, displayStyle: .collection)
  }
}

extension SortedSet: CustomStringConvertible, CustomDebugStringConvertible {
  /// A textual representation of this set.
  @inlinable
  public var description: String {
    let contents = self.map { String(reflecting: $0) }
    return "[" + contents.joined(separator: ", ") + "]"
  }

  /// A textual representation of this set, suitable for debugging.
  @inlinable
  public var debugDescription: String {
    return "SortedSet(" + description + ")"
  }
}
