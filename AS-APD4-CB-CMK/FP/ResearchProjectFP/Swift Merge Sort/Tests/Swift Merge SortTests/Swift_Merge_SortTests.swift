import XCTest
@testable import Swift_Merge_Sort

final class Swift_Merge_SortTests: XCTestCase {

    func testMergeEmptyLists() throws {
        XCTAssertEqual(
            Swift_Merge_Sort.mergeLists(
                leftList: [],
                rightList: []
            ),
            []
        )
    }

    func testMergeTinyLists() throws {
        XCTAssertEqual(
            Swift_Merge_Sort.mergeLists(
                leftList: [4, 3],
                rightList: [2, 1]
            ),
            [2, 1, 4, 3]
        )
    }

    func testMergeSortedLists() throws {
        XCTAssertEqual(
            Swift_Merge_Sort.mergeLists(
                leftList: [1, 2],
                rightList: [3, 4]
            ),
            [1, 2, 3, 4]
        )
    }

    func testAlreadySortedList() throws {
        XCTAssertEqual(
            Swift_Merge_Sort.isAlreadySorted(
                toAnalyse: [1, 2, 3, 4, 5, 5, 6, 7, 8, 9, 10]
            ),
            true
        )
    }

    func testAlreadySortedEmptyList() throws {
        XCTAssertEqual(
            Swift_Merge_Sort.isAlreadySorted(
                toAnalyse: []
            ),
            true
        )
    }

    func testNotSortedList() throws {
        XCTAssertEqual(
            Swift_Merge_Sort.isAlreadySorted(
                toAnalyse: [2, 1, 3, 4]
            ),
            false
        )
    }

    func testMergeSortWithEmptyList() throws {
        XCTAssertEqual(
            Swift_Merge_Sort.mergeSort(
                toSort: []
            ),
            []
        )
    }

    func testMergeWithOneElementList() throws {
        XCTAssertEqual(
            Swift_Merge_Sort.mergeSort(
                toSort: [1]
            ),
            [1]
        )
    }

    func testMergeSortAlreadySortedList() throws {
        XCTAssertEqual(
            Swift_Merge_Sort.mergeSort(
                toSort: [1, 2, 3, 4, 5]
            ),
            [1, 2, 3, 4, 5]
        )
    }

    func testMergeSortShortList() throws {
        XCTAssertEqual(
            Swift_Merge_Sort.mergeSort(
                toSort: [5, 4, 3, 2, 1]
            ),
            [1, 2, 3, 4, 5]
        )
    }

    func testMergeSortMediumList() throws {
        let listToSort = [
            21, 25, 24, 12, 3, 23, 22, 17, 23, 24, 18, 18, 7, 10, 9, 2, 4,
            16, 14, 9, 9, 14, 17, 7, 10, 25, 11, 3, 4, 13, 4, 25, 25, 22,
            9, 20, 20, 1, 13, 2, 23, 13, 20, 21, 6, 5, 7, 4, 7, 15
        ]

        let expectedRet = [
            1, 2, 2, 3, 3, 4, 4, 4, 4, 5, 6, 7, 7, 7, 7, 9, 9, 9, 9, 10, 10,
            11, 12, 13, 13, 13, 14, 14, 15, 16, 17, 17, 18, 18, 20, 20, 20,
            21, 21, 22, 22, 23, 23, 23, 24, 24, 25, 25, 25, 25
        ]

        XCTAssertEqual(
            Swift_Merge_Sort.mergeSort(
                toSort: listToSort
            ),
            expectedRet
        )
    }

    func testMergeSortBigList() throws {
        let listToSort = [
            41, 33, 4, 26, 91, 43, 53, 95, 21, 62, 2, 45, 78, 25, 46, 27, 96,
            70, 92, 80, 78, 4, 18, 46, 39, 63, 28, 67, 86, 95, 36, 47, 72, 37,
            65, 63, 12, 82, 39, 72, 19, 59, 41, 52, 26, 31, 41, 16, 39, 12, 7,
            46, 34, 64, 12, 52, 67, 39, 63, 30, 90, 89, 81, 53, 75, 71, 49, 3,
            76, 89, 73, 72, 7, 1, 20, 3, 60, 24, 71, 16, 96, 87, 28, 98, 59,
            5, 87, 95, 65, 7, 74, 52, 40, 8, 14, 63, 11, 8, 95, 60
        ]
        let expectedRet = [
            1, 2, 3, 3, 4, 4, 5, 7, 7, 7, 8, 8, 11, 12, 12, 12, 14, 16, 16,
            18, 19, 20, 21, 24, 25, 26, 26, 27, 28, 28, 30, 31, 33, 34, 36,
            37, 39, 39, 39, 39, 40, 41, 41, 41, 43, 45, 46, 46, 46, 47, 49,
            52, 52, 52, 53, 53, 59, 59, 60, 60, 62, 63, 63, 63, 63, 64, 65,
            65, 67, 67, 70, 71, 71, 72, 72, 72, 73, 74, 75, 76, 78, 78, 80,
            81, 82, 86, 87, 87, 89, 89, 90, 91, 92, 95, 95, 95, 95, 96, 96, 98
        ]

        XCTAssertEqual(
            Swift_Merge_Sort.mergeSort(
                toSort: listToSort
            ),
            expectedRet
        )
    }

    func testMergeSortBigListWithDuplicates() throws {
        let listToSort = [
            10, 20, 19, 2, 11, 18, 6, 6, 7, 17, 21, 4, 25, 6, 2, 10, 4, 1, 6,
            19, 25, 24, 6, 9, 14, 22, 23, 23, 13, 8, 22, 12, 14, 12, 1, 15, 1,
            22, 11, 1, 25, 12, 12, 25, 16, 17, 17, 8, 12, 1, 24, 20, 9, 22, 14,
            19, 9, 13, 2, 16, 21, 9, 6, 6, 11, 1, 8, 22, 11, 3, 13, 18, 25, 6,
            12, 15, 23, 17, 12, 3, 13, 17, 8, 17, 17, 8, 18, 15, 6, 25, 23, 15,
            7, 24, 11, 21, 25, 11, 16, 16, 15, 2, 17, 6, 15, 19, 13, 10, 11, 20,
            16, 7, 12, 24, 12, 25, 1, 9, 24, 16, 22, 4, 16, 1, 23, 15, 18, 2,
            21, 25, 24, 23, 21, 11, 21, 17, 14, 20, 20, 24, 13, 4, 8, 18, 22,
            10, 14, 7, 5, 1, 14, 17, 11, 11, 9, 10, 2, 1, 25, 14, 13, 16, 5,
            24, 5, 16, 1, 9, 24, 9, 17, 13, 21, 7, 23, 9, 21, 19, 15, 23, 5,
            10, 19, 6, 19, 16, 19, 9, 22, 6, 16, 2, 10, 17, 21, 7, 20, 6, 17, 19
        ]

        let expectedRet = [
            1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 3, 4, 4,
            4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7,
            7, 7, 7, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10,
            10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 12, 12,
            12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13, 14, 14,
            14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16,
            16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
            17, 17, 17, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19, 19,
            20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 21, 22, 22,
            22, 22, 22, 22, 22, 22, 23, 23, 23, 23, 23, 23, 23, 23, 24, 24, 24,
            24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25
        ]

        XCTAssertEqual(
            Swift_Merge_Sort.mergeSort(
                toSort: listToSort
            ),
            expectedRet
        )
    }
}
