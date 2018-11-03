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

/// An ordered mapping from comparable keys to arbitrary values.
/// Works like `Dictionary`, but provides a well-defined ordering for its
/// elements.
///
/// `SortedDictionary` is a struct with copy-on-write value semantics, like
/// Swift's standard collection types. It uses an in-memory B-tree for element
/// storage, whose individual nodes may be shared with other sorted dictionarys.
/// Modifying an element of a sorted dictionary whose storage is (partially or
/// completely) shared requires copying of only O(log(`count`)) elements. (Thus,
/// mutation of shared sorted dictionarys may be relatively cheaper than
/// dictionaries, which need to clone all elements.)
///
/// Lookup, insertion and removal of individual key-value pairs in a sorted
/// dictionary have logarithmic complexity. This is in contrast to
/// `Dictionary`'s best-case O(1) (worst-case O(n)) implementations for the same
/// operations. To make up for being typically slower, `SortedDictionary` always
/// keeps its elements in a well-defined order.
///
/// While independently looking up individual elements takes O(log(n)) time,
/// batch operations on lots of elements often complete faster than you might
/// expect. For example, iterating over a `SortedDictionary` using the generator
/// API requires O(n) time, just like a dictionary.
///
/// Due to its tree-based structure, `SortedDictionary` is able to provide
/// efficient implementations for several operations that would be slower with
/// dictionaries.
///
@_fixed_layout
public struct SortedDictionary<Key: Equatable, Value> {
  @_fixed_layout
  public struct Index: Comparable {
    @usableFromInline
    internal var _base: _BTreeIndex<Key, Value>

    @inlinable
    internal init(_ base: _BTreeIndex<Key, Value>) {
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
    internal var _base: _BTreeIterator<Key, Value>

    @inlinable
    internal init(_ base: _BTreeIterator<Key, Value>) {
      _base = base
    }

    /// Advance to the next element and return it, or return `nil` if no next
    /// element exists.
    ///
    /// - Complexity: Amortized O(1)
    @inlinable
    public mutating func next() -> Element? {
      if _base.state.isAtEnd { return nil }
      let result = _base.state.element
      _base.state.moveForward()
      return result
    }
  }

  @usableFromInline
  internal typealias Tree = _BTree<Key, Value>

  /// The B-tree that serves as storage.
  @usableFromInline
  internal var tree: Tree // fileprivate(set)

  @inlinable
  internal init(_ tree: Tree) {
    self.tree = tree
  }
}

extension SortedDictionary {
  /// Initialize a new sorted dictionary from an unsorted sequence of elements,
  /// using a stable sort algorithm.
  ///
  /// If the sequence contains elements with duplicate keys, only the last
  /// element is kept in the sorted dictionary.
  ///
  /// - Complexity: O(*n* * log(*n*)) where *n* is the number of items in
  /// `elements`.
  @inlinable
  public init<S: Sequence>(
    unsortedElements elements: S,
    areInIncreasingOrder: @escaping (Key, Key) -> Bool
  ) where S.Element == Element {
    self.tree = Tree(
      elements, dropDuplicates: true,
      areInIncreasingOrder: areInIncreasingOrder)
  }

  /// Initialize a new sorted dictionary from a sorted sequence of elements.
  ///
  /// If the sequence contains elements with duplicate keys, only the last
  /// element is kept in the sorted dictionary.
  ///
  /// - Complexity: O(*n*) where *n* is the number of items in `elements`.
  @inlinable
  public init<S: Sequence>(
    sortedElements elements: S,
    areInIncreasingOrder: @escaping (Key, Key) -> Bool
  ) where S.Element == Element {
    self.tree = Tree(
      sortedElements: elements, dropDuplicates: true,
      areInIncreasingOrder: areInIncreasingOrder)
  }

  /// Initialize a new empty sorted dictionary.
  @inlinable
  public init(areInIncreasingOrder: @escaping (Key, Key) -> Bool) {
    self.tree = Tree(areInIncreasingOrder: areInIncreasingOrder)
  }
}

extension SortedDictionary where Key: Comparable {
  /// Create an empty sorted dictionary using the ordering defined on `Key` by
  /// its `Comparable` conformance.
  @inlinable
  public init() {
    self.tree = Tree(areInIncreasingOrder: <)
  }

  /// Create a sorted dictionary from a finite sequence of items. The sequence
  /// need not be sorted.
  ///
  /// - Complexity: O(*n* * log(*n*)), where *n* is the number of items in the
  ///   sequence.
  public init<S: Sequence>(unsortedElements elements: S)
  where S.Element == Element {
    self.init(unsortedElements: elements, areInIncreasingOrder: <)
  }

  /// Create a sorted dictionary from a sorted finite sequence of items.
  ///
  /// - Complexity: O(*n*), where *n* is the number of items in the sequence.
  public init<S: Sequence>(
    sortedElements elements: S
  ) where S.Element == Element {
    self.init(sortedElements: elements, areInIncreasingOrder: <)
  }
}

extension SortedDictionary: ExpressibleByDictionaryLiteral
where Key: Comparable {
  /// Initialize a new sorted dictionary from the given elements.
  @inlinable
  public init(dictionaryLiteral elements: (Key, Value)...) {
    self.tree = Tree(elements, dropDuplicates: true, areInIncreasingOrder: <)
  }
}

extension SortedDictionary: SortedInsertableCollection {
  /// A predicate that returns `true` if its first argument should be ordered
  /// before its second argument; otherwise, `false`.
  @inlinable
  public var areInIncreasingOrder: (Key, Key) -> Bool {
    return tree.areInIncreasingOrder
  }

  /// Returns the index for the given key, or `nil` if the key is not present in
  /// this sorted dictionary.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public func index(for key: Key) -> Index? {
    guard let idx = tree.index(forKey: key) else {
      return nil
    }
    return Index(idx)
  }

  /// Returns the index of where the given key would be after insertion and
  /// whether a key already exists that is equal to the given key.
  ///
  /// - Returns: `keyAlreadyExists` must be return true if a key that is equal
  ///   to the given key already exists in the dictionary. `location` must
  ///   return the index where the given key would be inserted.
  /// - Complexity: O(log(*n*)), where n is the count of the dictionary.
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

  /// Inserts an element into the dictionary. The dictionary must remain sorted
  /// after the new element is inserted.
  ///
  /// - Returns: `inserted` must be false if the element was not inserted into
  ///   the dictionary, otherwise return true. `location` should return the
  ///   index of where the element was inserted or where it would have been
  ///   inserted.
  @inlinable
  @discardableResult
  mutating public func insert(
    _ element: (key: Key, value: Value)
  ) -> (inserted: Bool, location: Index) {
    // FIXME: don't use element to find index
    if let old = tree.insertOrFind(element) {
      return (false, Index(tree.index(forKey: old.0)!))
    } else {
      return (true, Index(tree.index(forKey: element.key)!))
    }
  }
}

extension SortedDictionary: BidirectionalCollection {
  public typealias Element = (key: Key, value: Value)

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

  /// The number of (key, value) pairs in this sorted dictionary.
  @inlinable
  public var count: Int {
    return tree.count
  }

  /// True iff this collection has no elements.
  @inlinable
  public var isEmpty: Bool {
    return count == 0
  }

  /// Returns the (key, value) pair at the given index.
  ///
  /// - Requires: `index` originated from an unmutated copy of this sorted
  ///   dictionary.
  /// - Complexity: O(1)
  @inlinable
  public subscript(index: Index) -> Element {
    return tree[index._base]
  }

  /// Return an iterator over all (key, value) pairs in this sorted dictionary,
  /// in ascending key order.
  @inlinable
  public func makeIterator() -> Iterator {
    return Iterator(tree.makeIterator())
  }

  /// Returns the successor of the given index.
  ///
  /// - Requires: `index` is a valid index of this sorted dictionary and it is
  ///   not equal to `endIndex`.
  /// - Complexity: Amortized O(1).
  @inlinable
  public func index(after index: Index) -> Index {
    return Index(tree.index(after: index._base))
  }

  /// Replaces the given index with its successor.
  ///
  /// - Requires: `index` is a valid index of this sorted dictionary and it is
  ///   not equal to `endIndex`.
  /// - Complexity: Amortized O(1).
  @inlinable
  public func formIndex(after index: inout Index) {
    tree.formIndex(after: &index._base)
  }

  /// Returns the predecessor of the given index.
  ///
  /// - Requires: `index` is a valid index of this sorted dictionary and it is
  ///   not equal to `startIndex`.
  /// - Complexity: Amortized O(1).
  @inlinable
  public func index(before index: Index) -> Index {
    return Index(tree.index(before: index._base))
  }

  /// Replaces the given index with its predecessor.
  ///
  /// - Requires: `index` is a valid index of this sorted dictionary and it is
  ///   not equal to `startIndex`.
  /// - Complexity: Amortized O(1).
  @inlinable
  public func formIndex(before index: inout Index) {
    tree.formIndex(before: &index._base)
  }

  /// Returns an index that is the specified distance from the given index.
  ///
  /// - Requires: `index` must be a valid index of this sorted dictionary.
  ///   If `n` is positive, it must not exceed the distance from `index` to
  ///   `endIndex`.
  ///   If `n` is negative, it must not be less than the distance from `index`
  ///   to `startIndex`.
  /// - Complexity: O(log(*count*)) where *count* is the number of elements in
  ///   the sorted dictionary.
  @inlinable
  public func index(_ i: Index, offsetBy n: Int) -> Index {
    return Index(tree.index(i._base, offsetBy: n))
  }

  /// Offsets the given index by the specified distance.
  ///
  /// - Requires: `index` must be a valid index of this sorted dictionary.
  ///   If `n` is positive, it must not exceed the distance from `index` to
  ///   `endIndex`.
  ///   If `n` is negative, it must not be less than the distance from `index`
  ///   to `startIndex`.
  /// - Complexity: O(log(*count*)) where *count* is the number of elements in
  ///   the sorted dictionary.
  @inlinable
  public func formIndex(_ i: inout Index, offsetBy n: Int) {
    tree.formIndex(&i._base, offsetBy: n)
  }

  /// Returns an index that is the specified distance from the given index,
  /// unless that distance is beyond a given limiting index.
  ///
  /// - Requires: `index` and `limit` must be valid indices in this sorted
  ///   dictionary. The operation must not advance the index beyond `endIndex`
  ///   or before `startIndex`.
  /// - Complexity: O(log(*count*)) where *count* is the number of elements in
  ///   the sorted dictionary.
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
  ///   dictionary. The operation must not advance the index beyond `endIndex`
  ///   or before `startIndex`.
  /// - Complexity: O(log(*count*)) where *count* is the number of elements in
  ///   the sorted dictionary.
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
  /// - Requires: `start` and `end` must be valid indices in this sorted
  ///   dictionary.
  /// - Complexity: O(1)
  @inlinable
  public func distance(from start: Index, to end: Index) -> Int {
    return tree.distance(from: start._base, to: end._base)
  }
}

extension SortedDictionary {
  /// Returns the index of the element at `offset`.
  ///
  /// - Requires: `offset >= 0 && offset < count`
  /// - Complexity: O(log(`count`))
  @inlinable
  public func index(atOffset offset: Int) -> Index {
    return Index(tree.index(ofOffset: offset))
  }

  /// Returns the offset of the element at `index`.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public func offset(of index: Index) -> Int {
    return tree.offset(of: index._base)
  }

  /// Returns the offset of the element with the given key, or `nil` if there is
  /// no such element.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public func offset(of key: Key) -> Int? {
    return tree.offset(forKey: key)
  }

  /// Return the element stored at `offset` in this sorted dictionary.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public subscript(offset offset: Int) -> Element {
    return tree.element(atOffset: offset)
  }

  /// Returns the sub sorted dictionary within an offset range
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public subscript(
    offset offsetRange: Range<Int>
  ) -> Slice<SortedDictionary> {
    let start = index(atOffset: offsetRange.lowerBound)
    let end = index(atOffset: offsetRange.upperBound)
    return self[start..<end]
  }

  /// Set the value of the element stored at `offset` in this sorted dictionary.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  @discardableResult
  public mutating func updateValue(
    _ value: Value,
    atOffset offset: Int
  ) -> Value {
    return tree.setValue(atOffset: offset, to: value)
  }
}

extension SortedDictionary {
  /// Call `body` on each element in `self` in ascending key order.
  ///
  /// - Complexity: O(*n*), where *n* is the length of the dictionary
  @inlinable
  public func forEach(_ body: (Element) throws -> Void) rethrows {
    try tree.forEach(body)
  }

  /// Return an `Array` containing the results of mapping `transform` over all
  /// elements in `self`. The elements are transformed in ascending key order.
  ///
  /// - Complexity: O(*n*), where *n* is the length of the dictionary
  @inlinable
  public func map<T>(_ transform: (Element) throws -> T) rethrows -> [T] {
    var result: [T] = []
    result.reserveCapacity(self.count)
    try self.forEach {
      result.append(try transform($0))
    }
    return result
  }

  /// Return an `Array` containing the concatenated results of mapping
  /// `transform` over `self`.
  ///
  /// - Complexity: O(*n*), where *n* is the length of the dictionary
  @inlinable
  public func flatMap<S: Sequence>(
    _ transform: (Element) throws -> S
  ) rethrows -> [S.Element] {
    var result: [S.Element] = []
    try self.forEach { element in
      result.append(contentsOf: try transform(element))
    }
    return result
  }

  /// Return an `Array` containing the non-`nil` results of mapping `transform`
  /// over `self`.
  ///
  /// - Complexity: O(*n*), where *n* is the length of the dictionary
  @inlinable
  public func compactMap<T>(
    _ transform: (Element) throws -> T?
  ) rethrows -> [T] {
    var result: [T] = []
    try self.forEach { element in
      if let t = try transform(element) {
        result.append(t)
      }
    }
    return result
  }

  /// Returns a new soretd dictionary containing the keys of this soretd
  /// dictionary with the values transformed by the given closure.
  ///
  /// - Parameter transform: A closure that transforms a value. `transform`
  ///   accepts each value of the soretd dictionary as its parameter and returns
  ///   a transformed value of the same or of a different type.
  /// - Returns: A sorted dictionary containing the keys and transformed values
  ///   of this dictionary.
  ///
  /// - Complexity: O(*n*), where *n* is the length of the dictionary.
  @inlinable
  public func mapValues<T>(
    _ transform: (Value) throws -> T
  ) rethrows -> SortedDictionary<Key, T> {
    var result = SortedDictionary<Key, T>(
      sortedElements: [], areInIncreasingOrder: areInIncreasingOrder)
    var i = startIndex
    while i < endIndex {
      result.insert((self[i].key, try transform(self[i].value)))
      formIndex(after: &i)
    }
    return result
  }

  /// Calculate the left fold of this sorted dictionary over `combine`:
  /// return the result of repeatedly calling `combine` with an accumulated
  /// value initialized to `initial` and each element of `self`, in turn. I.e
  ///
  ///     return `combine(combine(...combine(combine(initial, self[0]), self[1]),...self[count-2]), self[count-1])`.
  ///
  /// - Complexity: O(*n*), where *n* is the length of the dictionary
  @inlinable
  public func reduce<T>(
    _ initialResult: T,
    _ nextPartialResult: (T, Element) throws -> T
  ) rethrows -> T {
    var result = initialResult
    try self.forEach {
      result = try nextPartialResult(result, $0)
    }
    return result
  }
}

extension SortedDictionary {

  // FIXME: Use a custom wrapper
  @inlinable
  public var keys: SortedSet<Key> {
    return SortedSet(
      sortedElements: map { $0.0 },
      areInIncreasingOrder: areInIncreasingOrder)
  }

  /// A collection containing just the values in this sorted dictionary, in
  /// order of ascending keys.
  @inlinable
  public var values: LazyMapCollection<SortedDictionary<Key, Value>, Value> {
    return self.lazy.map { $0.1 }
  }

  /// Provides access to the value for a given key. Nonexistent values are
  /// represented as `nil`.
  ///
  /// - Complexity: O(log(*n*)), where *n* is the length of the dictionary
  @inlinable
  public subscript(key key: Key) -> Value? {
    get {
      return tree.value(of: key)
    }
    set(value) {
      if let value = value {
        updateValue(value, forKey: key)
      } else {
        removeValue(forKey: key)
      }
    }
  }

  /// Update the value stored in the sorted dictionary for the given key, or, if
  /// they key does not exist, add a new key-value pair to the sorted
  /// dictionary. Returns the value that was replaced, or `nil` if a new
  /// key-value pair was added.
  ///
  /// This method invalidates all existing indexes into `self`.
  ///
  /// - Complexity: O(log(*n*)), where *n* is the length of the dictionary
  @inlinable
  @discardableResult
  public mutating func updateValue(_ value: Value, forKey key: Key) -> Value? {
    return tree.insertOrReplace((key, value))?.1
  }
}

extension SortedDictionary {
  /// Combines elements from `self` with those in `other`. If a key is included
  /// in both sorted dictionaries, then strategy is used to decide which value
  /// to use.
  ///
  /// This function links subtrees containing elements with distinct keys when
  /// possible; this can drastically improve performance when the keys of the
  /// two sorted dictionarys aren't too interleaved.
  ///
  /// - Complexity: O(`count`)
  @inlinable
  public mutating func merge(
    _ other: SortedDictionary<Key, Value>,
    uniquingKeysWith strategy: (Value, Value) -> Value
  ) {
    self.tree.formUnion(other.tree, by: strategy)
  }

  /// Combines elements from `self` with those in `other`. If a key is included
  /// in both sorted dictionaries, then strategy is used to decide which value
  /// to use.
  ///
  /// This function links subtrees containing elements with distinct keys when
  /// possible; this can drastically improve performance when the keys of the
  /// two sorted dictionarys aren't too interleaved.
  ///
  /// - Complexity: O(`count`)
  @inlinable
  public mutating func merge<S: Sequence>(
    _ other: S,
    uniquingKeysWith strategy: (Value, Value) -> Value
  ) where S.Element == (Key, Value) {
    self.tree.formUnion(other, by: strategy)
  }

  /// Return a sorted dictionary that combines elements from `self` with those
  /// in `other`. If a key is included in both sorted dictionaries, then
  /// strategy is used to decide which value to use.
  ///
  /// This function links subtrees containing elements with distinct keys when
  /// possible; this can drastically improve performance when the keys of the
  /// two sorted dictionarys aren't too interleaved.
  ///
  /// - Complexity: O(`count`)
  @inlinable
  public func merging(
    _ other: SortedDictionary<Key, Value>,
    uniquingKeysWith strategy: (Value, Value) -> Value
  ) -> SortedDictionary {
    var result = self
    result.merge(other, uniquingKeysWith: strategy)
    return result
  }

  /// Return a sorted dictionary that combines elements from `self` with those
  /// in `other`. If a key is included in both sorted dictionaries, then
  /// strategy is used to decide which value to use.
  ///
  /// This function links subtrees containing elements with distinct keys when
  /// possible; this can drastically improve performance when the keys of the
  /// two sorted dictionarys aren't too interleaved.
  ///
  /// - Complexity: O(`count`)
  @inlinable
  public func merging<S: Sequence>(
    _ other: S,
    uniquingKeysWith strategy: (Value, Value) -> Value
  ) -> SortedDictionary where S.Element == (Key, Value) {
    var result = self
    result.merge(other, uniquingKeysWith: strategy)
    return result
  }
}


extension SortedDictionary {
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
    return tree.popLast()
  }

  /// Remove the key-value pair at `index` from this sorted dictionary.
  ///
  /// This method invalidates all existing indexes into `self`.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  @discardableResult
  public mutating func remove(at index: Index) -> (key: Key, value: Value) {
    return tree.remove(at: index._base)
  }

  /// Remove and return the (key, value) pair at the specified offset from the
  /// start of the sorted dictionary.
  ///
  /// - Complexity: O(log(*n*)), where *n* is the length of the dictionary
  @inlinable
  @discardableResult
  public mutating func remove(atOffset offset: Int) -> Element {
    return tree.remove(atOffset: offset)
  }

  /// Remove all (key, value) pairs in the specified offset range.
  ///
  /// - Complexity: O(log(*n*)), where *n* is the length of the dictionary
  @inlinable
  public mutating func remove(atOffset offset: Range<Int>) {
    precondition(
      offset.lowerBound >= 0 && offset.upperBound <= count,
      "offset must be between 0 and the length of the collection")
    tree.withCursor(atOffset: offset.lowerBound) { cursor in
      cursor.remove(offset.count)
    }
  }

  /// Remove a given key and the associated value from this sorted dictionary.
  /// Returns the value that was removed, or `nil` if the key was not present in
  /// the sorted dictionary.
  ///
  /// This method invalidates all existing indexes into `self`.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  @discardableResult
  public mutating func removeValue(forKey key: Key) -> Value? {
    return tree.remove(key)?.1
  }

  /// Remove and return the smallest member in this sorted dictionary.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  @discardableResult
  public mutating func removeFirst() -> Element {
    return tree.removeFirst()
  }

  /// Remove the smallest `n` members from this sorted dictionary.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  public mutating func removeFirst(_ n: Int) {
    tree.removeFirst(n)
  }

  /// Remove and return the largest member in this sorted dictionary.
  ///
  /// - Complexity: O(log(`count`))
  @inlinable
  @discardableResult
  public mutating func removeLast() -> Element {
    return tree.removeLast()
  }

  /// Remove the largest `n` members from this sorted dictionary.
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

  /// Remove all elements from this sorted dictionary.
  ///
  /// This method invalidates all existing indexes into `self`.
  ///
  /// - Complexity: O(`count`)
  @inlinable
  public mutating func removeAll() {
    tree = Tree(areInIncreasingOrder: tree.areInIncreasingOrder)
  }
}

extension SortedDictionary {
  /// Returns a new sorted dictionary containing the key-value pairs of the
  /// sorted dictionary that satisfy the given predicate.
  ///
  /// - Parameter isIncluded: A closure that takes a key-value pair as its
  ///   argument and returns a Boolean value indicating whether the pair
  ///   should be included in the returned dictionary.
  /// - Returns: A sorted dictionary of the key-value pairs that `isIncluded`
  ///   allows.
  @inlinable
  public __consuming func filter(
    _ isIncluded: (Element) throws -> Bool
  ) rethrows -> SortedDictionary<Key, Value> {
    var result = SortedDictionary<Key, Value>(
      areInIncreasingOrder: areInIncreasingOrder)
    for element in self {
      if try isIncluded(element) {
        result.insert((element.key, element.value))
      }
    }
    return result
  }
}

extension SortedDictionary {
  /// Return `true` iff `self` and `other` contain equivalent elements, using
  /// `isEquivalent` as the equivalence test.
  ///
  /// This method skips over shared subtrees when possible; this can drastically
  /// improve performance when the two sorted dictionarys are divergent
  /// mutations originating from the same value.
  ///
  /// - Requires: `isEquivalent` is an equivalence relation.
  /// - Complexity:  O(`count`)
  @inlinable
  public func elementsEqual(
    _ other: SortedDictionary,
    by isEquivalent: (Element, Element) throws -> Bool
  ) rethrows -> Bool {
    return try tree.elementsEqual(other.tree, by: isEquivalent)
  }
}

extension SortedDictionary: Equatable where Value: Equatable {
  /// Return `true` iff `self` and `other` contain equivalent elements.
  ///
  /// This method skips over shared subtrees when possible; this can drastically
  /// improve performance when the
  /// two sorted dictionarys are divergent mutations originating from the same
  /// value.
  ///
  /// - Complexity:  O(`count`)
  @inlinable
  public func elementsEqual(_ other: SortedDictionary) -> Bool {
    return tree.elementsEqual(other.tree)
  }

  /// Return true iff `a` is equal to `b`.
  ///
  /// This function skips over shared subtrees when possible; this can
  /// drastically improve performance when the two sorted dictionarys are
  /// divergent mutations originating from the same value.
  @inlinable
  public static func ==(a: SortedDictionary, b: SortedDictionary) -> Bool {
    return a.elementsEqual(b)
  }
}

extension SortedDictionary: Hashable where Key: Hashable, Value: Hashable {
  @inlinable
  public func hash(into hasher: inout Hasher) {
    tree.hash(into: &hasher)
  }
}

extension SortedDictionary.Iterator: CustomReflectable {
  /// A mirror that reflects the soretd dictionary iterator.
  public var customMirror: Mirror {
    return Mirror(
      self,
      children: EmptyCollection<(label: String?, value: Any)>())
  }
}

extension SortedDictionary: CustomReflectable {
  /// A mirror that reflects the sorted dictionary.
  public var customMirror: Mirror {
    let style = Mirror.DisplayStyle.dictionary
    return Mirror(self, unlabeledChildren: self, displayStyle: style)
  }
}

extension SortedDictionary: CustomStringConvertible {
  /// A textual representation of this sorted dictionary.
  @inlinable
  public var description: String {
    let contents = self.map { (key, value) -> String in
      let ks = String(reflecting: key)
      let vs = String(reflecting: value)
      return "\(ks): \(vs)"
    }
    return "[" + contents.joined(separator: ", ") + "]"
  }
}

extension SortedDictionary: CustomDebugStringConvertible {
  /// A textual representation of this sorted dictionary, suitable for
  /// debugging.
  @inlinable
  public var debugDescription: String {
    let contents = self.map { (key, value) -> String in
      let ks = String(reflecting: key)
      let vs = String(reflecting: value)
      return "\(ks): \(vs)"
    }
    return "[" + contents.joined(separator: ", ") + "]"
  }
}
