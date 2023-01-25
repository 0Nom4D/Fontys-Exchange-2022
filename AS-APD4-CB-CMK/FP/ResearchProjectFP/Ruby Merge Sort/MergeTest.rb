require_relative "MergeSort"
require "test/unit"

class TestMergeSort < Test::Unit::TestCase

    def test_MergeEmptyLists
        assert_equal([], mergeList([], []))
    end

    def test_MergeTinyLists
        assert_equal([2, 1, 4, 3], mergeList([4, 3], [2, 1]))
    end

    def test_MergeSortedLists
        assert_equal([1, 2, 3, 4], mergeList([1, 2], [3, 4]))
    end

    def test_isAlreadySortedFunc
        assert_equal(true, isAlreadySorted([1, 2, 3, 4, 5, 5, 6, 7, 8, 9, 10]))
    end

    def test_notAlreadySortedFunc
        assert_equal(false, isAlreadySorted([2, 1, 3, 4, 5, 5, 6, 7, 8, 9, 10]))
    end

    def test_variableImmutability
        unsortedList = [5, 4, 3, 2, 1]
        newList = mergeSort(unsortedList)
        assert_equal(unsortedList, [5, 4, 3, 2, 1])
        assert_equal(newList, [1, 2, 3, 4, 5])
    end

    def test_EmptyList
        assert_equal([], mergeSort([]))
    end

    def test_OneElementList
        assert_equal([1], mergeSort([1]))
    end

    def test_tinyListMergeSort
        assert_equal([1, 2, 3, 4, 5], mergeSort([5, 4, 3, 2, 1]))
    end

    def test_AlreadySortedList
        assert_equal([1, 2, 3, 4, 5], mergeSort([1, 2, 3, 4, 5]))
    end

    def test_UnsortedMediumList
        assert_equal(
            [ 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 4, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 9, 9, 10, 10, 10 ],
            mergeSort([ 6, 8, 2, 9, 5, 2, 8, 2, 6, 5, 7, 5, 7, 2, 5, 5, 6, 8, 6, 6, 3, 8, 7, 5, 1, 7, 1, 3, 4, 3, 2, 6, 1, 3, 1, 10, 9, 2, 2, 10, 2, 3, 2, 10, 8, 8, 3, 5, 5, 8 ])
        )
    end

end