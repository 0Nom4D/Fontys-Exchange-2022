#!/usr/bin/ruby

def mergeSort(list)
    if list.size <= 1 or isAlreadySorted(list)
        return list
    end
    midSize = list.size / 2
    mergeList(mergeSort(list[0, midSize]), mergeSort(list[midSize, list.size]))
end

def isAlreadySorted(list)
    list.each_cons(2).all?{|left, right| left <= right}
end

def mergeList(alist, blist)
    if alist.empty?
        return blist
    elsif blist.empty?
        return alist
    elsif alist[0] <= blist[0]
        return [alist[0]] + mergeList(alist[1, alist.length], blist)
    else
        return [blist[0]] + mergeList(alist, blist[1, blist.length])
    end
end
