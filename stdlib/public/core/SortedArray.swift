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

/// A sorted collection of comparable elements; also known as a multiset.
/// `SortedArray` is like a `SortedSet` except it can contain multiple members
/// that are equal to each other. Lookup, insertion and removal of any element
/// has logarithmic complexity.
///
/// `SortedArray` stores duplicate elements in their entirety; it doesn't just
/// count multiplicities. This is an important feature when equal elements can
/// be distinguished by identity comparison or some other means. (If you're OK
/// with just counting duplicates, use a `SortedDictionary` or a `Dictionary`
/// with the multiplicity as the value.)
///
/// `SortedArray` is a struct with copy-on-write value semantics.
/// It uses an in-memory b-tree for element storage, whose individual nodes may
/// be shared with other sorted sets or sorted arrays. Mutating a sorted array
/// whose storage is (partially or completely) shared requires copying of only
/// O(log(`count`)) elements. (Thus, mutation of shared `SortedArray`s may be
/// cheaper than ordinary `Set`s, which need to copy all elements.)
///
/// Set operations on sorted arrays (such as taking the union, intersection or
/// difference) can take as little as O(log(n)) time if the elements in the
/// input sorted arrays aren't too interleaved.
///
/// - SeeAlso: `SortedSet`
@_fixed_layout
public struct SortedArray<Element: Equatable> {
  @_fixed_layout
  public struct Index: Comparable {
    @usableFromInline
    internal var _base: _BTreeIndex<Element, Void>

    @inlinable
    internal init(_ base: _BTreeIndex<Element, Void>) {
      _base = base
    }

    @inlinable
    public static func <(lhs: Index, rhs: Index) -> Bool {
      return lhs._base < rhs._base
    }

    @inlinable
    public static func ==(lhs: Index, rhs: Index) -> Bool {
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

extension SortedArray {
  /// Create a sorted array from a finite sequence of items. The sequence need
  /// not be sorted.
  /// If the sequence contains duplicate items, all of them are kept, in the
  /// same order.
  ///
  /// - Complexity: O(*n* * log(*n*)), where *n* is the number of items in the
  ///   sequence.
  @inlinable
  public init<S: Sequence>(
    unsortedElements elements: S,
    areInIncreasingOrder: @escaping (Element, Element) -> Bool
  ) where S.Element == Element {
    let sortedElements = elements.sorted(by: areInIncreasingOrder)
      .lazy
      .map { (key: $0, value: ()) }
    self.init(Tree(
      sortedElements: sortedElements, dropDuplicates: false,
      areInIncreasingOrder: areInIncreasingOrder))
  }

  /// Create a sorted array from a sorted finite sequence of items.
  /// If the sequence contains duplicate items, all of them are kept.
  ///
  /// - Complexity: O(*n*), where *n* is the number of items in the sequence.
  @inlinable
  public init<S: Sequence>(
    sortedElements elements: S,
    areInIncreasingOrder: @escaping (Element, Element) -> Bool
  ) where S.Element == Element {
    let items = elements.lazy.map { (key: $0, value: ()) }
    self.init(Tree(
      sortedElements: items, dropDuplicates: false,
      areInIncreasingOrder: areInIncreasingOrder))
  }

  /// Create an empty sorted array.
  @inlinable
  public init(areInIncreasingOrder: @escaping (Element, Element) -> Bool) {
    self.tree = Tree(areInIncreasingOrder: areInIncreasingOrder)
  }
}

extension SortedArray where Key: Comparable {
  /// Create an empty sorted array using the ordering defined on `Element` by
  /// its `Comparable` conformance.
  @inlinable
  public init() {
    self.tree = Tree(areInIncreasingOrder: <)
  }

  /// Create a sorted array from a finite sequence of items. The sequence
  /// need not be sorted.
  ///
  /// - Complexity: O(*n* * log(*n*)), where *n* is the number of items in the
  ///   sequence.
  public init<S: Sequence>(unsortedElements elements: S)
  where S.Element == Element {
    self.init(unsortedElements: elements, areInIncreasingOrder: <)
  }

  /// Create a sorted array from a sorted finite sequence of items.
  ///
  /// - Complexity: O(*n*), where *n* is the number of items in the sequence.
  public init<S: Sequence>(
    sortedElements elements: S
  ) where S.Element == Element {
    self.init(sortedElements: elements, areInIncreasingOrder: <)
  }
}

extension SortedArray: ExpressibleByArrayLiteral where Element: Comparable {
  public typealias ArrayLiteralElement = Element

  /// Create a sorted array with the specified list of items.
  /// If the array literal contains duplicate items, all of them are kept.
  @inlinable
  public init(arrayLiteral elements: Element...) {
    self.init(unsortedElements: elements)
  }
}

extension SortedArray: SortedInsertableCollection {
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
  ///   to the given key already exists in the array, otherwise return
  ///   false. `location` must return the index where the given key would be
  ///   inserted.
  /// - Complexity: O(log(*n*)), where *n* is the count of the array.
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

  /// Inserts an element into the array. The array must remain sorted
  /// after the new element is inserted.
  ///
  /// - Returns: `inserted` must be false if the element was not inserted into
  ///   the array, otherwise return true. `location` should return the
  ///   index of where the element was inserted or where it would have been
  ///   inserted.
  /// - Complexity: O(log(*n*)), where *n* is the count of the array
  @inlinable
  @discardableResult
  public mutating func insert(
    _ element: Element
  ) -> (inserted: Bool, location: Index) {
    tree.insert((element, ()), at: .after)
    return (true, Index(tree.index(forKey: element)!))
  }
}

extension SortedArray: BidirectionalCollection {
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

  /// The number of elements in this sorted array.
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

  /// Return an iterator over all elements in this sorted array, in ascending
  /// key order.
  @inlinable
  public func makeIterator() -> Iterator {
    return Iterator(_BTreeKeyIterator(tree.makeIterator()))
  }

  /// Returns the successor of the given index.
  ///
  /// - Requires: `index` is a valid index of this sorted array and it is not
  ///   equal to `endIndex`.
  /// - Complexity: Amortized O(1).
  @inlinable
  public func index(after index: Index) -> Index {
    return Index(tree.index(after: index._base))
  }

  /// Replaces the given index with its successor.
  ///
  /// - Requires: `index` is a valid index of this sorted array and it is not
  ///   equal to `endIndex`.
  /// - Complexity: Amortized O(1).
  @inlinable
  public func formIndex(after index: inout Index) {
    tree.formIndex(after: &index._base)
  }

  /// Returns the predecessor of the given index.
  ///
  /// - Requires: `index` is a valid index of this sorted array and it is not
  ///   equal to `startIndex`.
  /// - Complexity: Amortized O(1).
  @inlinable
  public func index(before index: Index) -> Index {
    return Index(tree.index(before: index._base))
  }

  /// Replaces the given index with its predecessor.
  ///
  /// - Requires: `index` is a valid index of this sorted array and it is not
  ///   equal to `startIndex`.
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
  ///   the array.
  @inlinable
  public func formIndex(_ i: inout Index, offsetBy n: Int) {
    tree.formIndex(&i._base, offsetBy: n)
  }

  /// Returns an index that is at the specified distance from the given index,
  /// unless that distance is beyond a given limiting index.
  ///
  /// - Requires: `index` and `limit` must be valid indices in this sorted
  ///   array. The operation must not advance the index beyond `endIndex` or
  ///   before `startIndex`.
  /// - Complexity: O(log(*count*)) where *count* is the number of elements in
  ///   the array.
  @inlinable
  public func index(
    _ i: Index,
    offsetBy n: Int,
    limitedBy limit: Index
  ) -> Index? {
    guard let index = tree.index(
      i._base, offsetBy: n, limitedBy: limit._base) else {
        return nil
    }
    return Index(index)
  }

  /// Offsets the given index by the specified distance, or so that it equals
  /// the given limiting index.
  ///
  /// - Requires: `index` and `limit` must be valid indices in this sorted
  ///   array. The operation must not advance the index beyond `endIndex` or
  ///   before `startIndex`.
  /// - Complexity: O(log(*count*)) where *count* is the number of elements in
  ///   the sorted array.
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
  /// - Requires: `start` and `end` must be valid indices in this sorted array.
  /// - Complexity: O(1)
  @inlinable
  public func distance(from start: Index, to end: Index) -> Int {
    return tree.distance(from: start._base, to: end._base)
  }
}

extension SortedArray {
  /// Returns the offset of the element at `index`.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public func index(atOffset offset: Int) -> Index {
    return Index(tree.index(ofOffset: offset))
  }

  /// Returns the index of the element at `offset`.
  ///
  /// - Requires: `offset >= 0 && offset < count`
  /// - Complexity: O(log(`count`))
  @inlinable
  public func offset(of index: Index) -> Int {
    return tree.offset(of: index._base)
  }

  /// If `member` is in this sorted array, return the offset of its first
  /// instance. Otherwise, return `nil`.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public func offset(of member: Element) -> Int? {
    return tree.offset(forKey: member, choosing: .first)
  }

  /// Returns the element at `offset` from the start of the sorted array.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public subscript(offset offset: Int) -> Element {
    return tree.element(atOffset: offset).0
  }

  /// Returns the sub sorted array containing elements in the specified range of
  /// offsets from the start of the sorted array.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public subscript(
    offset offsetRange: Range<Int>
  ) -> Slice<SortedArray<Element>> {
    let start = index(atOffset: offsetRange.lowerBound)
    let end = index(atOffset: offsetRange.upperBound)
    return Slice(base: self, bounds: start..<end)
  }
}

extension SortedArray {
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
  public func flatMap<S : Sequence>(_ transform: (Element) throws -> S)
    rethrows -> [S.Element] {
      return try tree.flatMap { try transform($0.0) }
  }

  /// Return an `Array` containing the non-`nil` results of mapping `transform`
  /// over `self`.
  @inlinable
  public func compactMap<T>(_ transform: (Element) throws -> T?) rethrows -> [T] {
    return try tree.compactMap { try transform($0.0) }
  }

  /// Return an `Array` containing the elements of `self`, in ascending order,
  /// that satisfy the predicate `includeElement`.
  @inlinable
  public func filter(
    _ isIncluded: (Element) throws -> Bool
  ) rethrows -> [Element] {
    var result: [Element] = []
    try tree.forEach { e -> Void in
      if try isIncluded(e.0) {
        result.append(e.0)
      }
    }
    return result
  }

  /// Return the result of repeatedly calling `combine` with an accumulated
  /// value initialized to `initial` and each element of `self`, in turn.
  ///     return `combine(combine(...combine(combine(initial, self[0]), self[1]),...self[count-2]), self[count-1])`.
  @inlinable
  public func reduce<T>(
    _ initialResult: T,
    _ nextPartialResult: (T, Element) throws -> T
  ) rethrows -> T {
    return try tree.reduce(initialResult) { try nextPartialResult($0, $1.0) }
  }
}

extension SortedArray {
  /// Return (the first instance of) the smallest element in the sorted array,
  /// or `nil` if the sorted array is empty.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public var first: Element? { return tree.first?.0 }

  /// Return (the last instance of) the largest element in the sorted array, or
  /// `nil` if the sorted array is empty.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public var last: Element? { return tree.last?.0 }

  /// Return the smallest element in the sorted array, or `nil` if the sorted
  /// array is empty. This is the same as `first`.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public func min() -> Element? { return first }

  /// Return the largest element in the set, or `nil` if the set is empty. This
  /// is the same as `last`.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public func max() -> Element? { return last }
}

extension SortedArray {
  /// Return true if the sorted array contains `element`.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public func contains(_ element: Element) -> Bool {
    return tree.value(of: element) != nil
  }

  /// Returns the index of the first instance of a given member, or `nil` if the
  /// member is not present in the sorted array.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public func firstIndex(of member: Element) -> Index? {
    guard let index = tree.index(forKey: member, choosing: .first) else {
      return nil
    }
    return Index(index)
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

extension SortedArray {
  /// Inserts all the elements from another sorted array into this sorted array.
  @inlinable
  public mutating func insert(contentsOf other: SortedArray) {
    tree = tree.union(other.tree, by: .countingMatches)
  }

  /// Inserts all the elements from another sorted set into this sorted array.
  @inlinable
  public mutating func insert(contentsOf other: SortedSet<Element>) {
    tree = tree.union(other.tree, by: .countingMatches)
  }

  /// Inserts all the elements from a sequence into this sorted array.
  @inlinable
  public mutating func insert<S: Sequence>(contentsOf seq: S)
  where S.Element == Element {
    tree.formUnion(seq.map { (key: $0, value: ()) })
  }
}

extension SortedArray {
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

  /// Remove and return the largest member in this sorted array, or return `nil`
  /// if the sorted array is empty.
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
    precondition(
      offset.lowerBound >= 0 && offset.upperBound <= count,
      "offset must be between 0 and the length of the collection")
    tree.withCursor(atOffset: offset.lowerBound) { cursor in
      cursor.remove(offset.count)
    }
  }

  /// Remove and return the first instance of `member` from the sorted array,
  /// or return `nil` if the sorted array contains no instances of `member`.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  @discardableResult
  public mutating func remove(_ member: Element) -> Element? {
    return tree.remove(member, at: .first)?.0
  }

  /// Remove and return the smallest member in this sorted array.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  @discardableResult
  public mutating func removeFirst() -> Element {
    return tree.removeFirst().0
  }

  /// Remove the smallest `n` members from this sorted array.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public mutating func removeFirst(_ n: Int) {
    tree.removeFirst(n)
  }

  /// Remove and return the largest member in this sorted array.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  @discardableResult
  public mutating func removeLast() -> Element {
    return tree.removeLast().0
  }

  /// Remove the largest `n` members from this sorted array.
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

  /// Remove all members from this sorted array.
  @inlinable
  public mutating func removeAll() {
    tree.removeAll()
  }
}

extension SortedArray {
  /// Return an `Array` containing the members of this sorted array, in
  /// ascending order.
  ///
  /// `SortedSet` already keeps its elements sorted, so this is equivalent to
  /// `Array(self)`.
  ///
  /// - Complexity: O(`count`)
  @inlinable
  public func sorted() -> [Element] {
    // The sorted array is already sorted.
    return Array(self)
  }
}

extension SortedArray: Equatable {
  /// Return `true` iff `self` and `other` contain the same number of instances
  /// of all the same elements.
  ///
  /// This method skips over shared subtrees when possible; this can drastically
  /// improve performance when the two sorted arrays are divergent mutations
  /// originating from the same value.
  ///
  /// - Complexity:  O(`count`)
  @inlinable
  public func elementsEqual(_ other: SortedArray<Element>) -> Bool {
    return self.tree.elementsEqual(other.tree, by: { $0.0 == $1.0 })
  }

  /// Returns `true` iff `a` contains the exact same elements as `b`, including
  /// multiplicities.
  ///
  /// This function skips over shared subtrees when possible; this can
  /// drastically improve performance when the two sorted arrays are divergent
  /// mutations originating from the same value.
  ///
  /// - Complexity: O(`count`)
  @inlinable
  public static func ==(
    a: SortedArray<Element>,
    b: SortedArray<Element>
  ) -> Bool {
    return a.elementsEqual(b)
  }
}

extension SortedArray: Hashable where Key: Hashable {
  @inlinable
  public func hash(into hasher: inout Hasher) {
    for item in self {
      hasher.combine(item)
    }
  }
}

extension SortedArray: CustomReflectable {
  /// A mirror that reflects the sorted array.
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self, displayStyle: .collection)
  }
}

extension SortedArray: CustomStringConvertible, CustomDebugStringConvertible {
  /// A textual representation of this sorted array.
  @inlinable
  public var description: String {
    let contents = self.map { String(reflecting: $0) }
    return "[" + contents.joined(separator: ", ") + "]"
  }

  /// A textual representation of this sorted array, suitable for debugging.
  @inlinable
  public var debugDescription: String {
    return "SortedArray(" + description + ")"
  }
}
