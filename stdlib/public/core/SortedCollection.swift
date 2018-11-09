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

public protocol SortedCollection: Collection {
  associatedtype Key: Comparable
  associatedtype Keys: SortedCollection
    where Keys.Element == Key, Keys.Key == Key

  // Returns the index for the given key or `nil` of the key is not present.
  func index(for key: Key) -> Index?

  /// A sorted collection of all the keys for this collection.
  var keys: Keys { get }
}


public protocol SortedInsertableCollection: SortedCollection {
  /// Returns the index of where the given key would be after insertion and
  /// whether a key already exists that is equal to the given key.
  ///
  /// - Returns: `keyAlreadyExists` must be return true if a key that is equal
  ///   to the given key already exists in the collection, otherwise return
  ///   false. `location` must return the index where the given key would be
  ///   inserted.
  func insertionPoint(
    for key: Key
  ) -> (keyAlreadyExists: Bool, location: Index)

  /// Inserts an element into the collection. The collection must remain sorted
  /// after the new element is inserted.
  ///
  /// - Returns: `inserted` must be false if the element was not inserted into
  ///   the collection, otherwise return true. `location` should return the
  ///   index of where the element was inserted or where it would have been
  ///   inserted.
  mutating func insert(
    _ element: Element
  ) -> (inserted: Bool, location: Index)
}

extension SortedCollection {
  /// Returns the element that is associated with `key`.
  public subscript(key: Key) -> Element? {
    if let idx = index(for: key) {
      return self[idx]
    } else {
      return nil
    }
  }
}

extension SortedCollection where Keys == Self {
  public var keys: Self {
    return self
  }
}

extension SortedCollection where Key == Element {
  public func index(for key: Key) -> Index? {
    return firstIndex(of: key)
  }
}

extension SortedCollection where Self: RandomAccessCollection, Key == Element {
  public func index(for key: Key) -> Index? {
    var start = startIndex
    var end = endIndex

    while start < end {
      let mid = index(start, offsetBy: distance(from: start, to: end) / 2)
      if self[mid] == key {
        return mid
      } else if key < self[mid] {
        end = mid
      } else {
        start = index(after: mid)
      }
    }
    return nil
  }
}

extension SortedInsertableCollection where Key == Element {
  public func insertionPoint(
    for key: Key
  ) -> (keyAlreadyExists: Bool, location: Index) {
    guard startIndex < endIndex else {
      return (false, startIndex)
    }

    var i = startIndex
    var beforeEnd = startIndex
    while i < endIndex {
      if self[i] < key {
        beforeEnd = i
        formIndex(after: &i)
      } else {
        return (self[i] == key, i)
      }
    }
    return (self[beforeEnd] == key, endIndex)
  }
}

extension SortedInsertableCollection
where Self: RandomAccessCollection, Key == Element {
  public func insertionPoint(
    for key: Key
  ) -> (keyAlreadyExists: Bool, location: Index) {
    var start = startIndex
    var end = endIndex
    var keyAlreadyExists = false
    while start < end {
      let mid = index(start, offsetBy: distance(from: start, to: end) / 2)
      if self[mid] == key {
        keyAlreadyExists = true
      }
      if key < self[mid] {
        end = mid
      } else {
        start = index(after: mid)
      }
    }

    return (keyAlreadyExists, start)
  }
}
