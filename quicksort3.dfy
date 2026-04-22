predicate sorted(a:seq<int>, lo:nat, hi:nat)
  requires 0 <= lo <= hi <= |a|
{
    forall k :: lo <= k < hi - 1 ==> a[k] <= a[k + 1]
}

method QuickSortAll(a: array<int>)
  requires a.Length > 1
  modifies a
  ensures sorted(a[..], 0, a.Length-1)
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  QuickSort(a, 0, a.Length-1);
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
  requires 0 <= lo <= hi < |a| == |b|
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

method QuickSort(a:array<int>, lo:nat, hi:nat)
  modifies a
  requires 0 <= lo <= hi < a.Length
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures forall i :: 0 <= i < lo ==> a[i] == old(a[i])
  ensures forall i :: hi <= i < a.Length ==> a[i] == old(a[i]) 
  ensures sorted(a[..], lo, hi)
  decreases hi-lo
{
  // Ensure indices are in correct order
  if hi - lo <= 1
  {
    return;
  }
  else
  {
    // Partition array and get the pivot index
    var p := Partition(a, lo, hi);
    ghost var pivot := a[p];
        
    // Sort the two partitions
    // Left side of pivot
    ghost var preSortLeft := a[..];
    QuickSort(a, lo, p); 
    LemmaMultiset(a[..], preSortLeft[..], lo, p+1);
    LemmaMultisetPreservesLess(a[..], preSortLeft[..], pivot, lo, p+1);

    // Right side of pivot
    ghost var preSortRight := a[..];
    QuickSort(a, p+1, hi); 
    assert a[hi] == preSortRight[hi];
    LemmaMultiset(a[..], preSortRight[..], p+1, hi);
    LemmaMultisetPreservesGreater(a[..], preSortRight[..], pivot, p+1, hi);
  }
}

method Partition(a:array<int>, lo:nat, hi:nat) returns (p: nat)
  modifies a
  requires 0 <= lo < hi <= a.Length
  ensures lo <= p < hi
  ensures forall k :: lo <= k < p ==> a[k] <= a[p]
  ensures forall k :: p < k < hi ==> a[p] <= a[k]
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures forall i :: 0 <= i < a.Length && !(lo <= i < hi) ==> a[i] == old(a[i])
{
  // Choose the last element as the pivot
  var pivot := a[hi-1];

  var i := lo;
  var j := lo;

  while j < hi - 1 
    invariant lo <= i <= j < hi
    invariant a[hi - 1] == pivot
    invariant forall k :: lo <= k < i ==> a[k] <= pivot
    invariant forall k :: i <= k < j ==> a[k] > pivot
    invariant forall k :: 0 <= k < lo || hi <= k < a.Length ==> a[k] == old(a[k])
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases hi-j
  {
    // If the current element is less than or equal to the pivot
    if a[j] <= pivot
    {
      // Swap the current element with the element at the temporary pivot index
      Swap(a, i, j); 

      // Move the temporary pivot index forward
      i := i + 1;
    }
    j := j + 1;
  }

  // Swap the pivot with the last element
  Swap(a, i, hi - 1); 
  p := i;
}

method Swap(a: array<int>, i:nat, j:nat)
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
