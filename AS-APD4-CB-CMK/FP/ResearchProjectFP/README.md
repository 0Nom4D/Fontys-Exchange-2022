# Research on Functional Merge Sort

A merge sort implementation for Functional Programming Reseach Project.

This implementation is made with [Ruby](./Ruby%20Merge%20Sort/) and with [Swift](./Swift%20Merge%20Sort/).

## Ruby

### Ruby as a functional language

Firstly, we can give the functional paradigm 4 main concepts:

- Pure functions
- Recursions
- Immutability
- High orders functions and first-class functions.

Ruby is a multi-paradigm language. As written in the documentation of Ruby, the creators were looking to combine functional programming with imperative programming.

All blocks are inspired by functional languages.

From all listed concepts, Ruby have access to pure functions, recursions, immutability and higher order and first-class functions.

### Ruby Merge Sort Implementation

In order to launch the Merge Sort implementation, you will need to install [Ruby binary](https://www.ruby-lang.org/en/documentation/installation/).

Then, in order to test the project, you can use:

```txt
$> ruby MergeTest.rb
Loaded suite MergeTest
Started
......
Finished in 0.003862 seconds.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
6 tests, 7 assertions, 0 failures, 0 errors, 0 pendings, 0 omissions, 0 notifications
100% passed
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
1553.60 tests/s, 1812.53 assertions/s
```

This version is a functional programming implementation.

All variables from the code are immutables. Both functions (mergeSort and mergeLists) are high order and first class functions.

This version uses a lambda to check if the list passed as parameter is already sorted.

All functions are also pure.

For a given input, the function always will give the same output for given parameters. The mergeSort function will always give an ascending sorted array. The mergeLists function will also always give the same output for given parameters.

## Swift

### Swift as a functional language

Swift is a multi-paradigm language introduced by Apple in 2014. It is a derived language from Objective-C. It is also used in order to develop IOS Apps.

From all listed functional paradigms, Swift has access to pure functions, recursions, immutability (with the @frozen decorator), immutability and higher order and first-class functions.

### Swift Merge Sort Implementation

In order to launch the Swift Merge Sort Implementation, you will need to install [Swift](https://www.swift.org/getting-started/).

Then, in order to test the merge sort implementation, you can use the following command:

```txt
$> swift test
Building for debugging...
Build complete! (1.42s)
Test Suite 'All tests' started at 2022-09-30 13:54:16.600
Test Suite 'Swift Merge SortPackageTests.xctest' started at 2022-09-30 13:54:16.612
Test Suite 'Swift_Merge_SortTests' started at 2022-09-30 13:54:16.612
Test Case '-[Swift_Merge_SortTests.Swift_Merge_SortTests testMergeSortAlreadySortedList]' started.
Test Case '-[Swift_Merge_SortTests.Swift_Merge_SortTests testMergeSortAlreadySortedList]' passed (0.005 seconds).
Test Case '-[Swift_Merge_SortTests.Swift_Merge_SortTests testMergeSortBigList]' started.
Test Case '-[Swift_Merge_SortTests.Swift_Merge_SortTests testMergeSortBigList]' passed (0.002 seconds).
Test Case '-[Swift_Merge_SortTests.Swift_Merge_SortTests testMergeSortBigListWithDuplicates]' started.
Test Case '-[Swift_Merge_SortTests.Swift_Merge_SortTests testMergeSortBigListWithDuplicates]' passed (0.002 seconds).
Test Case '-[Swift_Merge_SortTests.Swift_Merge_SortTests testMergeSortMediumList]' started.
Test Case '-[Swift_Merge_SortTests.Swift_Merge_SortTests testMergeSortMediumList]' passed (0.001 seconds).
Test Case '-[Swift_Merge_SortTests.Swift_Merge_SortTests testMergeSortShortList]' started.
Test Case '-[Swift_Merge_SortTests.Swift_Merge_SortTests testMergeSortShortList]' passed (0.001 seconds).
Test Case '-[Swift_Merge_SortTests.Swift_Merge_SortTests testMergeSortWithEmptyList]' started.
Test Case '-[Swift_Merge_SortTests.Swift_Merge_SortTests testMergeSortWithEmptyList]' passed (0.000 seconds).
Test Case '-[Swift_Merge_SortTests.Swift_Merge_SortTests testMergeWithOneElementList]' started.
Test Case '-[Swift_Merge_SortTests.Swift_Merge_SortTests testMergeWithOneElementList]' passed (0.000 seconds).
Test Suite 'Swift_Merge_SortTests' passed at 2022-09-30 13:54:16.624.
         Executed 7 tests, with 0 failures (0 unexpected) in 0.011 (0.012) seconds
Test Suite 'Swift Merge SortPackageTests.xctest' passed at 2022-09-30 13:54:16.624.
         Executed 7 tests, with 0 failures (0 unexpected) in 0.011 (0.012) seconds
Test Suite 'All tests' passed at 2022-09-30 13:54:16.624.
         Executed 7 tests, with 0 failures (0 unexpected) in 0.011 (0.024) seconds
```

Just as the Ruby implementation, you can tell this is a functional implementation. Since the code is the same as the Ruby implementation, we can write everything we wrote for the Ruby implementation for the Swift implementation.

All variables are immutables through the code.

All functions are also pure. For a given input, the function always will give the same output for given parameters. The mergeSort function will always give an ascending sorted array. The mergeLists function will also always give the same output for given parameters.
