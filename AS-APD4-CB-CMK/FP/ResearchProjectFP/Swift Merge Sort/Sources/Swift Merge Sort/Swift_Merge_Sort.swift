func isAlreadySorted(toAnalyse: Array<Int>) -> Bool {
    var it = 0;

    while (it < toAnalyse.count - 1) {
        if (toAnalyse[it] > toAnalyse[it + 1]) {
            return false;
        }
        it += 1;
    }
    return true;
}

func mergeLists(leftList: Array<Int>, rightList: Array<Int>) -> Array<Int> {
    if (leftList.isEmpty) {
        return rightList;
    } else if (rightList.isEmpty) {
        return leftList;
    } else if (leftList[0] <= rightList[0]) {
        return [leftList[0]] + mergeLists(
            leftList: Array(leftList[1..<leftList.count]),
            rightList: rightList
        );
    }
    return [rightList[0]] + mergeLists(
        leftList: leftList,
        rightList: Array(rightList[1..<rightList.count])
    );
}

func mergeSort(toSort: Array<Int>) -> Array<Int> {
    if (toSort.count == 0 || isAlreadySorted(toAnalyse: toSort)) {
        return toSort;
    }
    let midOfList = toSort.count / 2;
    return mergeLists(
        leftList: mergeSort(
            toSort: Array(toSort[0..<midOfList])
        ),
        rightList: mergeSort(
            toSort: Array(toSort[midOfList..<toSort.count])
        )
    );
}
