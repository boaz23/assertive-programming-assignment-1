include "HeapSort-without-Main.dfy"

// TODO: implement using recursion;
// document each proof obligation, as we've learned, with assertion propagation and a lemma;
// don't forget to prove termination, after providing a definition to the variant function "V"
method HeapIncreaseKey(a: array<int>, i: nat, key: int)
	requires i < a.Length && a[i] < key
	requires hp(a[..])
	ensures hp(a[..])
	ensures multiset(a[..]) == multiset(old(a[..])[i := key])
	modifies a
	decreases V(a, i, key)

// TODO: provide a definition for this variant function (to help prove termination);
// do NOT change the signature of this function (even if you end up not using all its arguments)
function V(a: array<int>, i: nat, key: int): int

method {:verify false} Main() {
	var a: array<int> := new int[3];
	a[0], a[1], a[2] := 4, 8, 6;

	var q0: seq<int> := a[..];
	assert q0 == [4,8,6];
	HeapSort(a);
	assert multiset(a[..]) == multiset(q0);
	print "the sorted version of [4, 8, 6] is ";
	print a[..];
	assert Sorted(a);
	assert a[..] == [4,6,8];

	a := new int[5];
	a[0], a[1], a[2], a[3], a[4] := 3, 8, 5, -1, 10;
	q0 := a[..];
	assert q0 == [3, 8, 5, -1, 10];
	HeapSort(a);
	assert multiset(a[..]) == multiset(q0);
	print "\nthe sorted version of [3, 8, 5, -1, 10] is ";
	print a[..];
	assert Sorted(a);
	//assert a[..] == [-1, 3, 5, 8, 12];

	a[0], a[1], a[2], a[3], a[4] := 3, 8, 5, -1, 12;
	ghost var A := multiset(a[..]);
	MakeHeap(a, A);
	assert hp(a[..]);
	print "\nthe heap before increasing keys is ";
	print a[..];
	// a[..] == [12, 8, 5, -1, 3];
	ghost var q1 := a[..];
	HeapIncreaseKey(a, 3, 9);
	assert hp(a[..]);
	print "\ncontents of the heap after increasing to 9 the value of the element at index 3 is ";
	print a[..];
	//assert a[..] == [12, 9, 5, 8, 3];
	assert multiset(a[..]) == multiset(q1[3 := 9]); // == multiset([12, 9, 5, 8, 3]);
	ghost var q2 := a[..];
	HeapIncreaseKey(a, 4, 11);
	assert hp(a[..]);
	print "\ncontents of the heap after increasing to 11 the value of the element at index 4 is ";
	print a[..];
	//assert a[..] == [12, 11, 5, 8, 9];
	assert multiset(a[..]) == multiset(q2[4 := 11]); // == multiset([12, 11, 5, 8, 9]);

	assert AncestorIndex(0,0);
	assert AncestorIndex(0,1);
	assert AncestorIndex(0,2);
	assert AncestorIndex(0,3); // <0,1,3>
	assert AncestorIndex(0,4); // <0,1,4>
	assert !AncestorIndex(1,0);
	assert AncestorIndex(1,1);
	assert !AncestorIndex(1,2);
	assert AncestorIndex(1,3);
	assert AncestorIndex(1,4);
	assert !AncestorIndex(2,0);
	assert !AncestorIndex(2,1);
	assert AncestorIndex(2,2);
	assert !AncestorIndex(2,3);
	assert !AncestorIndex(2,4);
	assert AncestorIndex(2,5);
	assert AncestorIndex(2,6);
}
