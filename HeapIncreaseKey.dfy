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
{
	ghost var q := a[..]; // represents the updated state of `a`, updated when `a` changes.
	ghost var old_a := q; // stays 'constant' thorught the entire proof
	
	assert i < a.Length && a[i] < key;
	assert hp(q);

	if (i == 0) // please make RootIndex(nat) a predicate method
	{
		assert i < a.Length && a[i] < key;
		assert hp(q);
		assert i == 0;
		// ==>?
		assert hp(q[i := key]);
		assert multiset(q[i := key]) == multiset(old_a[i := key]);

		a[i] := key;
		q := a[..];

		assert q == a[..];
		assert hp(q);
		assert multiset(q) == multiset(old_a[i := key]);
	}
	else
	{
		assert i < a.Length && a[i] < key;
		assert hp(q);
		assert i > 0; // negation of the guard (outer if) and nat's are never negative
		// ==> slightly more compact form
		assert 0 < i < a.Length && a[i] < key;
		assert hp(q);

		var parentIndex := Parent(i);
		if (key <= a[parentIndex])
		{
			assert 0 < i < a.Length && a[i] < key;
			assert hp(q);
			assert key <= a[parentIndex]; // from the guard (inner if)
			// ==>?
			assert hp(q[i := key]);
			assert multiset(q[i := key]) == multiset(old_a[i := key]);

			a[i] := key;
			q := a[..];

			assert q == a[..];
			assert hp(q);
			assert multiset(q) == multiset(old_a[i := key]);
		}
		else
		{
			assert 0 < i < a.Length && a[i] < key;
			assert hp(q);
			assert a[parentIndex] < key; // negation of the guard (inner if)

			ghost var V0 := V(a, i, key);
			ghost var q' := q[i := q[parentIndex]];

			// for the pre-condition of the recursive call,
			// ensuring the next statement is ok
			HeapPropertyMaintained(a, q, q', i, parentIndex);
			a[i] := a[parentIndex];
			
			assert parentIndex < a.Length && a[parentIndex] < key; // for pre-condition of the recursive call
			assert 0 <= V(a, parentIndex, key) < V0; // for termination
			HeapIncreaseKey(a, parentIndex, key);
			q := a[..];

			assert q == a[..];
			assert hp(q); // by the recursive call post-condition
			assert multiset(q) == multiset(q'[parentIndex := key]); // by the recursive call post-condition
			// ==>?
			assert q == a[..];
			assert hp(q);
			assert multiset(q) == multiset(old_a[i := key]);
		}

		assert q == a[..];
		assert hp(q);
		assert multiset(q) == multiset(old_a[i := key]);
	}

	assert q == a[..];
	assert hp(q);
	assert multiset(q) == multiset(old_a[i := key]);
}

// TODO: provide a definition for this variant function (to help prove termination);
// do NOT change the signature of this function (even if you end up not using all its arguments)
function V(a: array<int>, i: nat, key: int): int
{
	i
}

lemma HeapPropertyMaintained(a: array<int>, q: seq<int>, q': seq<int>, i: nat, parentIndex: nat)
	requires 0 < i < a.Length
	requires parentIndex == Parent(i)
	requires q == a[..]
	requires q' == q[i := q[parentIndex]]
	requires hp(q)
	ensures hp(q')
{
	assert |q'| == |q|;

	assert AncestorIndex(parentIndex, i) by {
		assert parentIndex == Parent(i);
	}

	// show that for every 2 valid indices for q', they satisfy the heap property.
	forall i1, i2 : nat | 0 <= i1 < i2 < |q'| && AncestorIndex(i1, i2)
		ensures q'[i1] >= q'[i2]
	{
		if (i1 == i)
		{
			assert AncestorIndex(parentIndex, i2) by {
				assert AncestorIndex(parentIndex, i1) by {
					assert AncestorIndex(parentIndex, i);
					assert i1 == i;
				}
				assert AncestorIndex(i1, i2);
				AncestorIndexTransitive(parentIndex, i1, i2);
			}
			assert q'[i1] == q[parentIndex] >= q[i2] == q'[i2];
		}
		else if (i2 == i)
		{
			// dafny manages to proof this by herself as well
			// should we have written a proof to it?

			assert AncestorIndex(i1, parentIndex) by {
				assert i1 < i by {
					assert i1 < i2;
					assert i2 == i;
				}
				assert AncestorIndex(i1, i) by {
					assert AncestorIndex(i1, i2);
					assert i2 == i;
				}
				assert AncestorIndex(parentIndex, i);
				assert i1 <= parentIndex by {
					LeastNonSelfAncestor(i1, i, parentIndex);
				}

				MiddleAncestorIndex(i1, i2, parentIndex);
			}
			assert q'[i1] == q[i1] >= q[parentIndex] == q'[i] == q'[i2];
		}
		else
		{
			// dafny manages to proof this by herself as well
			// should we have written a proof to it?
			
			assert q'[i1] == q[i1] >= q[i2] == q'[i2];
		}
	}
}

lemma MiddleAncestorIndex(i1: nat, i2: nat, i3: nat)
	requires i1 < i2
	requires i1 <= i3
	requires AncestorIndex(i1, i2)
	requires AncestorIndex(i3, i2)
	ensures AncestorIndex(i1, i3)
{
	// dafny can handle this one herself
}

lemma LeastNonSelfAncestor(i1: nat, i2: nat, i3: nat)
	requires i1 < i2
	requires AncestorIndex(i1, i2)
	requires i3 == Parent(i2)
	ensures i1 <= i3
{
	// dafny can handle this one herself
}

lemma {:verify true} AncestorIndexTransitive(i1: nat, i2: nat, i3: nat)
	requires AncestorIndex(i1, i2)
	requires AncestorIndex(i2, i3)
	ensures AncestorIndex(i1, i3)
{
	// dafny can handle this one herself
}

// The 'cleaner' version
method {:verify true} HeapIncreaseKey'(a: array<int>, i: nat, key: int)
	requires i < a.Length && a[i] < key
	requires hp(a[..])
	ensures hp(a[..])
	ensures multiset(a[..]) == multiset(old(a[..])[i := key])
	modifies a
	decreases V(a, i, key)
{
	ghost var q := a[..];
	if (i == 0) // please make RootIndex(nat) a predicate method
	{
		a[i] := key;
	}
	else
	{
		var parentIndex := Parent(i);
		if (key <= a[parentIndex])
		{
			a[i] := key;
		}
		else
		{
			ghost var q' := q[i := q[parentIndex]];
			HeapPropertyMaintained(a, q, q', i, parentIndex);
			a[i] := a[parentIndex];
			HeapIncreaseKey(a, parentIndex, key);
		}
	}
}

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
