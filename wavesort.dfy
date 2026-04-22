predicate sorted(a:seq<int>, lo:nat, hi:nat)
  requires 0 <= lo <= hi < |a|
{
    forall k :: lo <= k < hi ==> a[k] <= a[k + 1]
}

method waveSort(s: array<int>)
  requires s.Length > 1
  modifies s
  ensures sorted(s[..], 0, s.Length-1)
  ensures multiset(s[..]) == multiset(old(s[..]))
{
    if s.Length < 2 
    {
        return;
    }
    upwave(s, 0, s.Length-1);
}

method upwave(s: array<int>, start: int, end: int)
    modifies s
    requires s.Length > 1
    requires 0 <= start <= end < s.Length
    ensures sorted(s[..], start, end)
    ensures forall i :: 0 <= i < start ==> s[i] == old(s[i])
    ensures forall i :: end < i < s.Length ==> s[i] == old(s[i]) 
    ensures multiset(s[..]) == multiset(old(s[..]))
    decreases end-start, 1
{
    if start == end
    {
        return;
    }
    var sortedStart := end;
    var sortedLength := 1;
    var leftBound := end - 1;
    var length := end - start + 1;

    while length > sortedLength 
      invariant sortedLength == end - sortedStart + 1
      invariant 1 <= sortedLength <= length
      invariant start <= leftBound < sortedStart <= end
      invariant multiset(s[..]) == multiset(old(s[..]))
      invariant sorted(s[..], sortedStart, end)
      invariant multiset(s[..]) == multiset(old(s[..]))
      invariant forall i :: 0 <= i < start ==> s[i] == old(s[i])
      invariant forall i :: end < i < s.Length ==> s[i] == old(s[i]) 
      decreases length-sortedLength
    {
        ghost var preDownwave := s[..];
        downwave(s, leftBound, sortedStart, end);
        sortedStart := leftBound;
        sortedLength := end - sortedStart + 1;
        //if length < sortedLength<<2
        if length < sortedLength * (2*2)
        {
            break;
        }
        //leftBound = end - sortedLength<<1 + 1
        leftBound := end - sortedLength*(2*1) + 1;
    }
    downwave(s, start, sortedStart, end);
}

method {:vcs_split_on_every_assert} downwave(s: array<int>, start: int, sortedStart: int, end: int)
    modifies s
    requires s.Length > 1
    requires 0 <= start <= end < s.Length
    requires start <= sortedStart <= end
    requires sorted(s[..], sortedStart, end)
    ensures sorted(s[..], start, end)
    ensures multiset(s[..]) == multiset(old(s[..]))
    ensures forall i :: 0 <= i < start ==> s[i] == old(s[i])
    ensures forall i :: end < i < s.Length ==> s[i] == old(s[i]) 
    decreases end-start, 0
{
    if sortedStart-start == 0
    {
        return;
    }
    var p := sortedStart + (end-sortedStart)/2;
    var m := partition(s, start, sortedStart, p);
    if m == sortedStart {
      if p == sortedStart {
        ghost var preLeft := s[..];
        upwave(s, start, sortedStart-1);
        assert sorted(s[..], start, sortedStart - 1);

        assert s[sortedStart] == preLeft[sortedStart];
        LemmaMultiset(s[..], preLeft[..], start, sortedStart);
        LemmaMultisetPreservesLess(s[..], preLeft[..], s[sortedStart], start, sortedStart);
        assert forall k :: start <= k < sortedStart ==> s[k] <= s[sortedStart];

        LemmaSortedEqualSlice(s[..], sortedStart, end, preLeft[..], sortedStart, end);
        assert sorted(s[..], sortedStart, end);
        assert forall k :: sortedStart < k <= end ==> s[sortedStart] <= s[k];

        LemmaStitchSortedAroundPivot(s[..], start, sortedStart, end);
        return;
      }
      ghost var preDownwaveP := s[..];
      LemmaLiftLeftBoundFromPrefixAndSorted(preDownwaveP, start, sortedStart, p);
      downwave(s, start, sortedStart, p-1);
      assert sorted(s[..], p, end);
      LemmaMultiset(s[..], preDownwaveP[..], start, p);
      LemmaMultisetPreservesLess(s[..], preDownwaveP[..], s[p], start, p);
      return;
    }

    LemmaSortedSubrange(s[..], sortedStart, p, end);
    assert sorted(s[..], sortedStart, p);

    assert forall k :: m <= k < sortedStart ==> s[k] >= s[p];

    LemmaLiftLeftBoundFromPrefixAndSorted(s[..], sortedStart, sortedStart, p);
    assert forall k :: sortedStart <= k < p ==> s[k] <= s[p];

    ghost var preSwap := s[..];
    blockSwap(s, m, sortedStart, p);
    if m == start {
      if p == sortedStart {
        ghost var preSortRight := s[..];
        assert forall k :: m < k <= end ==> preSortRight[m] <= preSortRight[k];
        upwave(s, m+1, end);

        assert sorted(s[..], m+1, end);
        LemmaPreservesGreaterOnRangePointwise(s[..], preSortRight[..], s[m], m+1, end+1);
        assert forall k :: m < k <= end ==> s[m] <= s[k];
        return;
      }
      ghost var preDownwaveRight := s[..];
      ghost var pivotPos := m + p - sortedStart;
      LemmaLiftRightBoundFromBlockSwap(preSwap[..], s[..], pivotPos, p, end);
      p := p + 1;
      downwave(s, m+p-sortedStart, p, end);
      LemmaPreservesGreaterOnRangePointwise(s[..], preDownwaveRight[..], s[pivotPos], pivotPos, end+1);
      return;
    }
    if p == sortedStart {
      assert s[m] == preSwap[p];
      LemmaLiftLeftBoundFromBlockSwap(preSwap[..], s[..], start, m, p);
      assert forall k :: start <= k < m ==> s[k] <= s[m];

      assert sorted(preSwap[..], p, end);
      LemmaLiftRightBoundFromBlockSwap(preSwap[..], s[..], m, p, end);
      assert forall k :: m < k <= end ==> s[m] <= s[k];

      ghost var prePivotSplit := s[..];
      upwave(s, start, m-1);
      assert s[m] == prePivotSplit[m];
      LemmaMultiset(s[..], prePivotSplit[..], start, m);
      LemmaMultisetPreservesLess(s[..], prePivotSplit[..], s[m], start, m);
      assert forall k :: start <= k < m ==> s[k] <= s[m];

      ghost var preSortRight := s[..];
      upwave(s, m+1, end);
      LemmaPreservesGreaterOnRangePointwise(s[..], preSortRight[..], s[m], m+1, end+1);
      assert forall k :: m < k <= end ==> s[m] <= s[k];
      return;
    }
    ghost var pivotPos := m + (p - sortedStart);

    LemmaSortedEqualSlice(s[..], m, pivotPos, preSwap, sortedStart, p);
    assert sorted(s[..], m, pivotPos);
    assert sorted(preSwap[..], p, end);
    LemmaLiftRightBoundFromBlockSwap(preSwap[..], s[..], pivotPos, p, end);
    assert forall k :: pivotPos < k <= end ==> s[pivotPos] <= s[k];
    assert sorted(s[..], p+1, end);

    ghost var preSortLeft := s[..];
    downwave(s, start, m, m+p-sortedStart-1);

    LemmaMultiset(s[..], preSortLeft[..], start, pivotPos);
    LemmaMultisetPreservesLess(s[..], preSortLeft[..], s[pivotPos], start, pivotPos);
    assert sorted(s[..], start, pivotPos - 1);
    assert s[pivotPos - 1] <= s[pivotPos];
    LemmaSortedExtendRight(s[..], start, pivotPos - 1);
    assert sorted(s[..], start, pivotPos);
    assert forall k :: start <= k < pivotPos ==> s[k] <= s[pivotPos];
    assert sorted(s[..], p+1, end);

    ghost var preRight := s[..];
    downwave(s, m+p-sortedStart+1, p+1, end);

    LemmaEqualSliceFromPointwise(s[..], preRight[..], start, pivotPos + 1);
    assert sorted(s[..], start, pivotPos);
    LemmaLiftLeftBoundFromPrefixAndSorted(s[..], start, start, pivotPos);

    LemmaSortedSubrange(s[..], start, pivotPos - 1, pivotPos);
    assert sorted(s[..], pivotPos + 1, end);
    LemmaPreservesGreaterOnRangePointwise(s[..], preRight[..], s[pivotPos], pivotPos + 1, end + 1);
    assert forall k :: pivotPos < k <= end ==> s[pivotPos] <= s[k];
    LemmaStitchSortedAroundPivot(s[..], start, pivotPos, end);
    return;
}

// p is the pivot index
// r is first sorted element
// l is index of left bound of unsorted part
method partition(s: array<int>, l: int, r: int, p:int) returns (i: int)
  modifies s
  requires 0 <= l < r < s.Length
  requires r <= p < s.Length
  ensures l <= i <= r
  ensures forall k :: l <= k < i ==> s[k] <= s[p]
  // returns pivot that lies in the greater part
  ensures forall k :: i <= k < r ==> s[p] <= s[k]
  ensures forall k,ll :: l <= k < i && i <= ll < r ==> s[k] <= s[ll]
  ensures multiset(s[..]) == multiset(old(s[..]))
  ensures forall k :: 0 <= k < s.Length && !(l <= k < r) ==> s[k] == old(s[k])
{
    var pivot := s[p];

    i := l - 1;
    var j := r;
    while true
        invariant multiset(s[..]) == multiset(old(s[..]))
        invariant l-1 <= i < j <= r
        invariant forall k :: l <= k <= i ==> s[k] <= pivot
        invariant forall k :: j <= k < r ==> s[k] >= pivot
        invariant forall k :: 0 <= k < s.Length && !(l <= k < r) ==> s[k] == old(s[k])
        decreases j-i
    {
        while true
            invariant multiset(s[..]) == multiset(old(s[..]))
            invariant l-1 <= i < j <= r
            invariant forall k :: l <= k <= i ==> s[k] <= pivot
            invariant forall k :: j <= k < r ==> s[k] >= pivot
            invariant forall k :: 0 <= k < s.Length && !(l <= k < r) ==> s[k] == old(s[k])
            decreases j-i
        {
            i := i+1;
            if i == j
            {
              return i;
            }
            if pivot < s[i]
            {
              break;
            }
        }
        while true
            invariant multiset(s[..]) == multiset(old(s[..]))
            invariant l <= i < j <= r
            invariant forall k :: l <= k < i ==> s[k] <= pivot
            invariant s[i] > pivot
            invariant forall k :: j <= k < r ==> s[k] >= pivot
            invariant forall k :: 0 <= k < s.Length && !(l <= k < r) ==> s[k] == old(s[k])
            decreases j
        {
            j := j-1;
            if j == i
            {
              return i;
            }
            if s[j] < pivot
            {
              break;
            }
        }
        Swap(s, i, j);
    }
}

method blockSwap(s: array<int>, m: int, r: int, p: int)
    modifies s
    requires 0 <= m <= r
    requires r <= p < s.Length
    requires sorted(s[..], r, p)
    requires forall k :: m <= k < r ==> s[k] >= s[p]
    requires forall k :: r <= k < p ==> s[k] <= s[p]
    // requires forall k :: m+p-r < k < r ==> s[k] >= s[m+p-r]
    ensures forall i :: 0 <= i < m ==> s[i] == old(s[i])
    ensures forall i :: p < i < s.Length ==> s[i] == old(s[i]) 
    ensures s[m..m+(p-r+1)] == old(s[r..p+1])
    ensures sorted(s[..], m, m+(p-r))
    ensures multiset(s[..]) == multiset(old(s[..]))
    // ensure less than/greater than pivot properties
    ensures forall k :: m <= k <= m+(p-r) ==> s[k] <= s[m+(p-r)]
    ensures forall k :: m+(p-r) < k <= p ==> s[k] >= s[m+(p-r)]
    ensures s[m+(p-r)] == old(s[p])
{
    // length of left block
    var ll := r - m;
    if ll == 0
    {
        return;
    }
    //length of right block
    var lr := p - r + 1;

    if lr <= ll
    {
        // if length of right block is shorter than left block
        blockSwap_sr(s, m, r, p);
    }
    else
    {
        assert forall k :: m+ll <= k < p ==> s[k] <= s[p] by {
          forall k | m+ll <= k < p
            ensures s[k] <= s[p]
          {
            assert m + ll == r;
            assert r <= k < p;
            SortedImpliesOrdered(s[..], r, p, k, p);
          }
        }
        blockSwap_sl(s, m, p, ll);
    }
}

method blockSwap_sr(s: array<int>, m: int, r: int, p: int)
    modifies s
    requires 0 <= m < r <= p < s.Length
    requires r-m >= p-r+1
    requires sorted(s[..], r, p)
    requires forall k :: m <= k < r ==> s[k] >= s[p]
    requires forall k :: r <= k < p ==> s[k] <= s[p]
    ensures sorted(s[..], m, m+(p-r))
    ensures forall k :: 0 <= k < m       ==> s[k] == old(s[k])
    ensures forall k :: p < k < s.Length ==> s[k] == old(s[k]) 
    ensures s[m+(p-r)+1..r] == old(s[m+(p-r)+1..r])
    ensures s[m..m+(p-r+1)] == old(s[r..p+1])
    ensures s[m+p-r] == old(s[p])
    ensures multiset(s[..]) == multiset(old(s[..]))
    // ensure less than/greater than properties
    ensures forall k :: m <= k <= m+p-r ==> s[k] <= s[m+p-r]
    ensures forall k :: m+p-r < k < r ==> s[k] >= s[m+p-r]
    ensures forall k :: r <= k <= p ==> s[k] >= s[m+p-r]
{
    ghost var old_s := s[..];

    var i := m;
    var tmp := s[i];
    var j := r;

    while j < p
        invariant m <= i < j < s.Length
        invariant m <= i <= m+(p-r)
        invariant i == m+j-r
        invariant r <= j <= p
        invariant forall k :: j <= k <= p ==> s[k] == old(s[k])

        invariant s[..m] == old(s[..m])
        invariant s[i+1..r] == old(s[i+1..r])
        invariant s[m+(p-r)+1..r] == old(s[m+(p-r)+1..r])
        invariant s[p+1..] == old(s[p+1..])

        invariant s[m..i] == old(s[r..j])
        invariant s[r..j] == old(s[m+1..i+1])

        decreases p-j
    {
        // 1. set s[m] to s[r]
        //    set s[r] to s[m+1]
        // 2. set s[m+1] to s[r+1]
        //    set s[r+1] to s[m+2]
        // 3. set s[m+2] to s[r+2]
        //    set s[r+2] to s[m+3]
        //.....
        s[i] := s[j];
        i := i + 1;
        s[j] := s[i];
        j := j + 1;
    }
    s[i] := s[j];
    s[j] := tmp;

    LemmaMultisetRightSwapPreserved(m, r, p, s, old_s);
    LemmaSortedEqualSlice(s[..], m, m+p-r, old_s[..], r, p);

    assert sorted(s[..], m, m+(p-r));
    assert s[m+p-r] == old_s[p];
    assert forall k :: m+p-r < k < r ==> s[k] == old_s[k];
    assert s[r..p] == old_s[m+1..m+p-r+1];
    assert forall k :: r <= k < p ==> s[k] == old_s[m+1+(k-r)];
    assert forall k :: r <= k <= p ==> s[k] >= old_s[p];
    assert forall k :: m <= k <= m+p-r ==> s[k] <= s[m+p-r] by {
      forall k | m <= k <= m+p-r
        ensures s[k] <= s[m+p-r]
      {
        SortedImpliesOrdered(s[..], m, m+p-r, k, m+p-r);
      }
    }
}

method blockSwap_sl(s: array<int>, m:int, p:int, ll:int)
    modifies s
    requires 0 < 2 * ll < p-m+1
    requires 0 <= m < p < s.Length
    requires sorted(s[..], m+ll, p)
    requires forall k :: m <= k < m+ll==> s[k] >= s[p]
    requires forall k :: m+ll <= k < p ==> s[k] <= s[p]
    ensures sorted(s[..], m, p-ll)
    ensures forall k :: 0 <= k < m       ==> s[k] == old(s[k])
    ensures forall k :: p < k < s.Length ==> s[k] == old(s[k]) 
    ensures s[m..p-ll+1] == old(s[m+ll..p+1])
    ensures s[p-ll+1..p+1] == old(s[m..m+ll])
    ensures multiset(s[..]) == multiset(old(s[..]))
    // ensure less than/greater than properties
    ensures s[p-ll] == old(s[p])
    ensures forall k :: m <= k <= p-ll ==> s[k] <= s[p-ll]
    ensures forall k :: p-ll <= k <= p ==> s[k] >= s[p-ll]
{
  ghost var old_s := s[..];
  var tmp := s[..];
  forall i | m <= i <= p-ll {
    s[i] := tmp[i+ll];
  }
  forall i | p-ll+1 <= i <= p {
    s[i] := tmp[m+(i-(p-ll+1))];
  }
  
  assert s[..m] == old_s[..m];
  assert s[p+1..] == old_s[p+1..];
  // sorted block swapped
  assert s[m..p-ll+1] == old_s[m+ll..p+1];
  // unsorted block swapped
  assert s[p-ll+1..p+1] == old_s[m..m+ll];

  LemmaMultisetLeftSwapPreserved(m, p, ll, s, old_s);
  LemmaBlockSwapSlOrdering(old_s, s[..], m, p, ll);
}

method Swap(a: array<int>, i:int, j:int)
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  modifies a
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
{
  if i != j
  {
    var t := a[i];
    a[i] := a[j];
    a[j] := t;
  }
}

// Lemmas needed for proof
lemma LemmaSortedAroundPivot(a: seq<int>, lo: int, pivot: int, hi: int)
  requires 0 <= lo <= pivot <= hi < |a|
  requires lo < pivot ==> sorted(a, lo, pivot - 1)
  requires pivot < hi ==> sorted(a, pivot + 1, hi)
  requires forall k :: lo <= k < pivot ==> a[k] <= a[pivot]
  requires forall k :: pivot < k <= hi ==> a[pivot] <= a[k]
  ensures sorted(a, lo, hi)
{
  assert forall k :: lo <= k < hi ==> a[k] <= a[k+1] by {
    forall k | lo <= k < hi
      ensures a[k] <= a[k+1]
    {
      if k < pivot - 1 {
        assert a[k] <= a[k+1];
      } else if k == pivot - 1 {
        assert a[k] <= a[pivot];
      } else if k == pivot {
        assert a[pivot] <= a[k+1];
      } else {
        assert a[k] <= a[k+1];
      }
    }
  }
}

lemma LemmaLiftLeftBoundFromBlockSwap(pre: seq<int>, post: seq<int>, lo: int, pivotPos: int, oldPivot: int)
  requires |pre| == |post|
  requires 0 <= lo <= pivotPos <= oldPivot < |pre|
  requires post[pivotPos] == pre[oldPivot]
  requires forall k :: lo <= k < pivotPos ==> post[k] == pre[k]
  requires forall k :: lo <= k < pivotPos ==> pre[k] <= pre[oldPivot]
  ensures forall k :: lo <= k < pivotPos ==> post[k] <= post[pivotPos]
{
  forall k | lo <= k < pivotPos
    ensures post[k] <= post[pivotPos]
  {
    assert post[k] == pre[k];
    assert post[pivotPos] == pre[oldPivot];
  }
}

lemma LemmaLiftRightBoundFromBlockSwap(pre: seq<int>, post: seq<int>, pivotPos: int, oldPivot: int, hi: int)
  requires |pre| == |post|
  requires 0 <= pivotPos <= oldPivot <= hi < |pre|
  requires post[pivotPos] == pre[oldPivot]
  requires forall k :: pivotPos < k <= oldPivot ==> post[pivotPos] <= post[k]
  requires forall k :: oldPivot < k <= hi ==> post[k] == pre[k]
  requires sorted(pre, oldPivot, hi)
  ensures forall k :: pivotPos < k <= hi ==> post[pivotPos] <= post[k]
{
  forall k | pivotPos < k <= hi
    ensures post[pivotPos] <= post[k]
  {
    if k <= oldPivot {
      assert post[pivotPos] <= post[k];
    } else {
      assert post[pivotPos] == pre[oldPivot];
      assert post[k] == pre[k];
      SortedImpliesOrdered(pre, oldPivot, hi, oldPivot, k);
    }
  }
}

lemma LemmaLiftLeftBoundFromPrefixAndSorted(a: seq<int>, lo: int, mid: int, pivot: int)
  requires 0 <= lo <= mid <= pivot < |a|
  requires forall k :: lo <= k < mid ==> a[k] <= a[pivot]
  requires sorted(a, mid, pivot)
  ensures forall k :: lo <= k < pivot ==> a[k] <= a[pivot]
{
  forall k | lo <= k < pivot
    ensures a[k] <= a[pivot]
  {
    if k < mid {
      assert a[k] <= a[pivot];
    } else {
      SortedImpliesOrdered(a, mid, pivot, k, pivot);
    }
  }
}

lemma LemmaStitchSortedAroundPivot(a: seq<int>, lo: int, pivot: int, hi: int)
  requires 0 <= lo <= pivot <= hi < |a|
  requires lo < pivot ==> sorted(a, lo, pivot - 1)
  requires pivot < hi ==> sorted(a, pivot + 1, hi)
  requires forall k :: lo <= k < pivot ==> a[k] <= a[pivot]
  requires forall k :: pivot < k <= hi ==> a[pivot] <= a[k]
  ensures sorted(a, lo, hi)
{
  LemmaSortedAroundPivot(a, lo, pivot, hi);
}

lemma LemmaMultisetPreservesLess(a:seq<int>, b:seq<int>, elem:int, i:nat, j:nat)
  requires |a|==|b| && i<=j<=|a|
  requires multiset(a[..]) == multiset(b[..])
  requires multiset(a[i..j]) == multiset(b[i..j])
  requires forall k : int :: i <= k < j ==> b[k] <= elem
  ensures forall k : int :: i <= k < j ==> a[k] in multiset(a[i..j])
  ensures forall k : int :: i <= k < j ==> a[k] <= elem
{
}

lemma SortedImpliesOrdered(a: seq<int>, lo: int, hi: int, i: int, j: int)
  requires 0 <= lo <= i <= j <= hi < |a|
  requires sorted(a, lo, hi)
  ensures a[i] <= a[j]
{
  if i < j {
    SortedImpliesOrdered(a, lo, hi, i, j-1);
    assert a[j-1] <= a[j];
  }
}

lemma LemmaMultisetPreservesGreater(a:seq<int>, b:seq<int>, elem: int, i:nat, j:nat)
  requires |a|==|b| && i<=j<=|a|
  requires multiset(a[..]) == multiset(b[..])
  requires multiset(a[i..j]) == multiset(b[i..j])
  requires forall k : int :: i <= k < j ==> b[k] >= elem 
  ensures forall k : int :: i <= k < j ==> a[k] in multiset(a[i..j])
  ensures forall k : int :: i <= k < j ==> a[k] >= elem
{
}

lemma MultisetCancelMiddle<T>(X: multiset<T>, A: multiset<T>, B: multiset<T>, Y: multiset<T>)
  requires X + A + Y == X + B + Y
  ensures  A == B
{
  forall v : T
    ensures A[v] == B[v]
  {
    assert (X + A + Y)[v] == (X + B + Y)[v];

    assert (X + A + Y)[v] == X[v] + A[v] + Y[v];
    assert (X + B + Y)[v] == X[v] + B[v] + Y[v];

    calc {
      X[v] + A[v] + Y[v];
      ==  X[v] + B[v] + Y[v];
    }
    assert A[v] == B[v];
  }
}

lemma MiddleFromWhole<T>(p: seq<T>, m1: seq<T>, m2: seq<T>, s: seq<T>)
  requires multiset(p + m1 + s) == multiset(p + m2 + s)
  ensures  multiset(m1) == multiset(m2)
{
  MultisetCancelMiddle(multiset(p), multiset(m1), multiset(m2), multiset(s));
}

lemma LemmaMultiset<T>(a: seq<T>, b: seq<T>, lo: nat, hi: nat)
  requires 0 <= lo <= hi <= |a| == |b|
  requires multiset(a) == multiset(b)
  requires a[0..lo] == b[0..lo]
  requires a[hi..] == b[hi..]
  ensures multiset(a[0..lo] + a[lo..hi] + a[hi..]) == multiset(b[0..lo] + b[lo..hi] + b[hi..])
  ensures multiset(a[lo..hi]) == multiset(b[lo..hi])
{
    assert b[..] == b[0..lo] + b[lo..hi] + b[hi..];
    assert a[..] == a[0..lo] + a[lo..hi] + a[hi..];
    assert multiset(a[..]) ==
        multiset(a[0..lo]) + multiset(a[lo..hi]) + multiset(a[hi..]);
    assert multiset(b[..]) ==
        multiset(b[0..lo]) + multiset(b[lo..hi]) + multiset(b[hi..]);
    assert multiset(a[..]) == multiset(b[..]);
    assert a[0..lo] == b[0..lo];
    assert multiset(a[0..lo]) == multiset(b[0..lo]);
    assert a[hi..] == b[hi..];
    assert multiset(a[hi..]) == multiset(b[hi..]);
    MiddleFromWhole(a[0..lo], a[lo..hi], b[lo..hi], a[hi..]);
    assert multiset(a[lo..hi]) == multiset(b[lo..hi]);
}

lemma LemmaSortedSubrange(a: seq<int>, lo: int, mid: int, hi: int)
  requires 0 <= lo <= mid <= hi < |a|
  requires sorted(a, lo, hi)
  ensures sorted(a, lo, mid)
  ensures sorted(a, mid, hi)
{
}

lemma LemmaSortedEqualSlice(a: seq<int>, alo: int, ahi: int, b: seq<int>, blo: int, bhi: int)
  requires 0 <= alo <= ahi < |a|
  requires 0 <= blo <= bhi < |b|
  requires ahi - alo == bhi - blo
  requires a[alo..ahi+1] == b[blo..bhi+1]
  requires sorted(b, blo, bhi)
  ensures sorted(a, alo, ahi)
{
  assert forall k :: alo <= k < ahi ==> a[k] <= a[k + 1] by {
    forall k | alo <= k < ahi
      ensures a[k] <= a[k + 1]
    {
      var t := k - alo;
      assert 0 <= t < |a[alo..ahi+1]| - 1;
      assert a[k] == a[alo..ahi+1][t];
      assert a[k + 1] == a[alo..ahi+1][t + 1];
      assert a[alo..ahi+1][t] == b[blo..bhi+1][t];
      assert a[alo..ahi+1][t + 1] == b[blo..bhi+1][t + 1];
      assert b[blo + t] == b[blo..bhi+1][t];
      assert b[blo + t + 1] == b[blo..bhi+1][t + 1];
      assert blo + t < bhi;
      assert b[blo + t] <= b[blo + t + 1];
    }
  }
}

lemma LemmaEqualSliceFromPointwise<T>(a: seq<T>, b: seq<T>, lo: int, hi: int)
  requires |a| == |b|
  requires 0 <= lo <= hi <= |a|
  requires forall i :: lo <= i < hi ==> a[i] == b[i]
  ensures a[lo..hi] == b[lo..hi]
{
  if lo < hi {
    LemmaEqualSliceFromPointwise(a, b, lo, hi - 1);
    assert a[lo..hi] == a[lo..hi-1] + [a[hi-1]];
    assert b[lo..hi] == b[lo..hi-1] + [b[hi-1]];
    assert a[hi-1] == b[hi-1];
  }
}

lemma LemmaPreservesGreaterOnRangePointwise(a: seq<int>, b: seq<int>, elem: int, lo: nat, hi: nat)
  requires |a| == |b|
  requires lo <= hi <= |a|
  requires multiset(a[..]) == multiset(b[..])
  requires forall i {:trigger a[i]} :: 0 <= i < lo ==> a[i] == b[i]
  requires forall i {:trigger a[i]} :: hi <= i < |a| ==> a[i] == b[i]
  requires forall k {:trigger b[k]} :: lo <= k < hi ==> b[k] >= elem
  ensures forall k :: lo <= k < hi ==> a[k] >= elem
{
  LemmaEqualSliceFromPointwise(a, b, 0, lo);
  LemmaEqualSliceFromPointwise(a, b, hi, |a|);
  LemmaMultiset(a, b, lo, hi);
  LemmaMultisetPreservesGreater(a, b, elem, lo, hi);
}

lemma LemmaSliceConcatMultiset<T>(s: seq<T>, i: int, j: int, k: int)
  requires 0 <= i <= j <= k <= |s|
  ensures multiset(s[i..k]) == multiset(s[i..j]) + multiset(s[j..k])
{
  // if pieces make up an array, then the whole is a multiset
  assert s[i..k] == s[i..j] + s[j..k];
}

lemma LemmaMultisetRightSwapPreserved(m: int, r: int, p: int, s: array<int>, old_s: seq<int>)
  requires s.Length == |old_s|
  requires 0 <= m < r <= p < s.Length
  requires r-m >= p-r+1

  // parts of array UNCHANGED
  requires s[..m] == old_s[..m]
  requires s[m+(p-r)+1..r] == old_s[m+(p-r)+1..r]
  requires s[p+1..] == old_s[p+1..]

  // parts of array CHANGED
  requires s[m..m+(p-r)+1] == old_s[r..p+1]
  requires s[r..p] == old_s[m+1..m+(p-r)+1]
  requires s[p] == old_s[m]

  ensures multiset(s[..]) == multiset(old_s[..])
{
  assert s[..] == s[..m] + s[m..p+1] + s[p+1..];
  assert old_s[..] == old_s[..m] + old_s[m..p+1] + old_s[p+1..];
  assert old_s[m..m+(p-r)+1] == [old_s[m]] + old_s[m+1..m+(p-r)+1];

  // section of array changed between m and p+1
  // split this into sections with known properties
  calc {
    multiset(s[m..p+1]);
    == { LemmaSliceConcatMultiset(s[..], m, r, p+1); }
    multiset(s[m..r]) + multiset(s[r..p+1]);
    == { LemmaSliceConcatMultiset(s[..], m, m+(p-r)+1, r); }
    multiset(s[m..m+(p-r)+1]) + multiset(s[m+(p-r)+1..r]) + multiset(s[r..p+1]);
    == { LemmaSliceConcatMultiset(s[..], r, p, p+1); }
    multiset(s[m..m+(p-r)+1]) + multiset(s[m+(p-r)+1..r]) + multiset(s[r..p]) + multiset(s[p..p+1]);
    == // now reconstruct the old array
    multiset(old_s[m+(p-r)+1..r]) + multiset(old_s[r..p+1]) + multiset(old_s[m+1..m+(p-r)+1]) + multiset([old_s[m]]);
    == { LemmaSliceConcatMultiset(old_s, m, m+1, m+(p-r)+1);}
    multiset(old_s[m..m+(p-r)+1]) + multiset(old_s[m+(p-r)+1..r]) + multiset(old_s[r..p+1]);
    == { LemmaSliceConcatMultiset(old_s, m, m+(p-r)+1, r);}
    multiset(old_s[m..r]) + multiset(old_s[r..p+1]);
    == { LemmaSliceConcatMultiset(old_s, m, r, p+1);}
    multiset(old_s[m..p+1]);
  }
}

lemma LemmaMultisetLeftSwapPreserved(m: int, p: int, ll: int, s: array<int>, old_s: seq<int>)
  requires s.Length == |old_s|
  requires 0 < 2 * ll < p - m + 1
  requires 0 <= m < p < s.Length
  requires s[..m] == old_s[..m]
  requires s[p+1..] == old_s[p+1..]
  requires s[m..p-ll+1] == old_s[m+ll..p+1]
  requires s[p-ll+1..p+1] == old_s[m..m+ll]
  ensures multiset(s[..]) == multiset(old_s[..])
{
  assert s[..] == s[..m] + s[m..p-ll+1] + s[p-ll+1..p+1] + s[p+1..];
  assert old_s[..] == old_s[..m] + old_s[m..m+ll] + old_s[m+ll..p+1] + old_s[p+1..];

  calc {
    multiset(s[..]);
    == { LemmaSliceConcatMultiset(s[..], 0, p+1, s.Length); }
    multiset(s[..p+1]) + multiset(s[p+1..]);
    == { LemmaSliceConcatMultiset(s[..], 0, m, p+1); }
    multiset(s[..m]) + multiset(s[m..p+1])  + multiset(s[p+1..]);
    == { LemmaSliceConcatMultiset(s[..], m, p-ll+1, p+1); }
    multiset(s[..m]) + multiset(s[m..p-ll+1]) + multiset(s[p-ll+1..p+1]) + multiset(s[p+1..]);
    ==
    multiset(old_s[..m]) + multiset(old_s[m+ll..p+1]) + multiset(old_s[m..m+ll]) + multiset(old_s[p+1..]);
    ==
    multiset(old_s[..m]) + multiset(old_s[m..m+ll]) + multiset(old_s[m+ll..p+1]) + multiset(old_s[p+1..]);
    == { LemmaSliceConcatMultiset(old_s, m, m+ll, p+1); }
    multiset(old_s[..m]) + multiset(old_s[m..p+1]) + multiset(old_s[p+1..]);
    == { LemmaSliceConcatMultiset(old_s, 0, m, p+1); }
    multiset(old_s[..p+1]) + multiset(old_s[p+1..]);
    == { LemmaSliceConcatMultiset(old_s, 0, p+1, s.Length); }
    multiset(old_s[..]);
  }
}

lemma LemmaBlockSwapSlOrdering(pre: seq<int>, post: seq<int>, m: int, p: int, ll: int)
  requires |pre| == |post|
  requires 0 < 2 * ll < p - m + 1
  requires 0 <= m < p < |pre|
  requires post[m..p-ll+1] == pre[m+ll..p+1]
  requires post[p-ll+1..p+1] == pre[m..m+ll]
  requires sorted(pre, m+ll, p)
  requires forall k :: m <= k < m+ll ==> pre[k] >= pre[p]
  requires forall k :: m+ll <= k < p ==> pre[k] <= pre[p]
  ensures sorted(post, m, p-ll)
  ensures post[p-ll] == pre[p]
  ensures forall k :: m <= k <= p-ll ==> post[k] <= post[p-ll]
  ensures forall k :: p-ll <= k <= p ==> post[k] >= post[p-ll]
{
  LemmaSortedEqualSlice(post, m, p-ll, pre, m+ll, p);
  assert post[p-ll] == pre[p];

  assert forall k :: m <= k <= p-ll ==> post[k] <= post[p-ll] by {
    forall k | m <= k <= p-ll
      ensures post[k] <= post[p-ll]
    {
      SortedImpliesOrdered(post, m, p-ll, k, p-ll);
    }
  }

  assert forall k :: p-ll <= k <= p ==> post[k] >= post[p-ll] by {
    forall k | p-ll <= k <= p
      ensures post[k] >= post[p-ll]
    {
      if k == p-ll {
      } else {
        var t := k - (p - ll + 1);
        assert 0 <= t < |post[p-ll+1..p+1]|;
        assert post[k] == post[p-ll+1..p+1][t];
        assert post[p-ll+1..p+1][t] == pre[m..m+ll][t];
        assert pre[m + t] == pre[m..m+ll][t];
        assert m <= m + t < m + ll;
        assert pre[m + t] >= pre[p];
      }
    }
  }
}

lemma LemmaSortedExtendRight(a: seq<int>, lo: int, hi: int)
  requires 0 <= lo <= hi < |a| - 1
  requires sorted(a, lo, hi)
  requires a[hi] <= a[hi + 1]
  ensures sorted(a, lo, hi + 1)
{
  assert forall k :: lo <= k < hi + 1 ==> a[k] <= a[k + 1] by {
    forall k | lo <= k < hi + 1
      ensures a[k] <= a[k + 1]
    {
      if k < hi {
        assert a[k] <= a[k + 1];
      } else {
        assert k == hi;
        assert a[k] <= a[hi + 1];
        assert k + 1 == hi + 1;
      }
    }
  }
}
