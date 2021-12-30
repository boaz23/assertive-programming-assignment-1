method Main()
{
	var q := [1,2,4,5,6,7,10,23];
	assert Sorted(q);
	assert HasAddends(q,10) by { assert q[2]+q[4] == 4+6 == 10; }
	var i,j := FindAddends(q, 10);
	print "Searching for addends of 10 in q == [1,2,4,5,6,7,10,23]:\n";
	print "Found that q[";
	print i;
	print "] + q[";
	print j;
	print "] == ";
	print q[i];
	print " + ";
	print q[j];
	print " == 10";
	assert i == 2 && j == 4;
}

predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}

predicate HasAddends(q: seq<int>, x: int)
{
	exists i,j :: 0 <= i < j < |q| && q[i] + q[j] == x
}

predicate IsValidIndex<T>(q: seq<T>, i: nat)
{
	0 <= i < |q|
}

predicate AreOreredIndices<T>(q: seq<T>, i: nat, j: nat)
{
	0 <= i < j < |q|
}

predicate AreAddendsIndices(q: seq<int>, x: int, i: nat, j: nat)
	requires IsValidIndex(q, i) && IsValidIndex(q, j)
{
	q[i] + q[j] == x
}

predicate HasAddendsInIndicesRange(q: seq<int>, x: int, i: nat, j: nat)
	requires AreOreredIndices(q, i, j)
{
	exists i', j' :: i <= i' < j' <= j < |q| && AreAddendsIndices(q, x, i', j')
}

predicate LoopInv(q: seq<int>, x: int, i: nat, j: nat, sum: int)
{
	AreOreredIndices(q, i, j) && HasAddendsInIndicesRange(q, x, i, j) && AreAddendsIndices(q, sum, i, j)
}

lemma {:verify true} HasAddendsOnEntry(q: seq<int>, x: int)
	requires HasAddends(q, x)
	ensures HasAddendsInIndicesRange(q, x, 0, |q| - 1)
{
	calc {
		HasAddends(q, x);
		==
		exists i, j :: 0 <= i < j < |q| && q[i] + q[j] == x;
		== { assert forall i, j :: (0 <= i < j < |q|) ==> (0 <= i < j <= |q| - 1 < |q|); }
		exists i, j :: 0 <= i < j <= |q| - 1 < |q| && q[i] + q[j] == x;
		== {
			// Extracting this to a lemma doesn't work for some reason
			assert |q| > 1;
			assert 0 <= 0 < |q|;
			assert 0 <= |q| - 1 < |q|;
			assert forall i, j :: 0 <= i < j <= |q| - 1 < |q| && q[i] + q[j] == x ==> AreAddendsIndices(q, x, i, j);
		}
		exists i, j :: 0 <= i < j <= |q| - 1 < |q| && AreAddendsIndices(q, x, i, j);
		==
		HasAddendsInIndicesRange(q, x, 0, |q| - 1);
	}
}

lemma LoopInvOnEntry(q: seq<int>, x: int, i: nat, j: nat, sum: int)
	requires sorted: Sorted(q)
	requires hasAddends: HasAddends(q, x)
	requires indices: i == 0 && j == |q| - 1
	requires sum: sum == q[i] + q[j]
	ensures LoopInv(q, x, i, j, sum)
{
	assert |q| > 1 by {
		reveal hasAddends;
	}
	assert AreOreredIndices(q, i, j) by {
		reveal indices;
	}
	assert HasAddendsInIndicesRange(q, x, i, j) by {
		reveal hasAddends;
		HasAddendsOnEntry(q, x);
		reveal indices;
	}
	assert AreAddendsIndices(q, sum, i, j) by {
		reveal sum;
	}
}

method FindAddends'(q: seq<int>, x: int) returns (i: nat, j: nat)
	requires Sorted(q) && HasAddends(q, x)
	ensures i < j < |q| && q[i] + q[j] == x
{
	i := 0;
	j := |q| - 1;
	var sum := q[i] + q[j];
	
	LoopInvOnEntry(q, x, i, j, sum);
	while sum != x
		invariant LoopInv(q, x, i, j, sum)
		decreases j - i
	{
		if (sum > x)
		{
			// Sum it too big, lower it by decreasing the high index
			j := j - 1;
		}
		// 'sum == x' cannot occur because the loop's guard is 'sum !=x'.
		else // (sum < x)
		{
			// Sum is too small, make it bigger by increasing the low index.
			i := i + 1;
		}

		sum := q[i] + q[j];
	}
}

method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
	requires Sorted(q) && HasAddends(q, x)
	ensures i < j < |q| && q[i]+q[j] == x
{
	i := 0;
	j := |q| - 1;
	var sum := q[i] + q[j];
	
	LoopInvOnEntry(q, x, i, j, sum);
	while sum != x
		invariant LoopInv(q, x, i, j, sum)
		decreases j - i
	{
		assert Sorted(q) && HasAddends(q, x); // from method's pre-condition
		assert sum != x; // from loop guard;
		assert LoopInv(q, x, i, j, sum); // from loop invariant

		if (sum > x)
		{
			// Sum it too big, lower it by decreasing the high index
			assert Sorted(q) && HasAddends(q, x); // from method's pre-condition
			assert sum != x; // from loop guard;
			assert LoopInv(q, x, i, j, sum); // from loop invariant
			assert sum > x; // from the if guard
			// ==>?
			assert LoopInv(q, x, i, j - 1, q[i] + q[j - 1]);
			j := j - 1;
			assert LoopInv(q, x, i, j, q[i] + q[j]);
		}
		// 'sum == x' cannot occur because the loop's guard is 'sum !=x'.
		else // (sum < x)
		{
			// Sum is too small, make it bigger by increasing the low index.
			assert Sorted(q) && HasAddends(q, x); // from method's pre-condition
			assert sum != x; // from loop guard;
			assert LoopInv(q, x, i, j, sum); // from loop invariant
			assert sum < x; // from the negation of the if guard
			// ==>?
			assert LoopInv(q, x, i + 1, j, q[i + 1] + q[j]);
			i := i + 1;
			assert LoopInv(q, x, i, j, q[i] + q[j]);
		}

		assert LoopInv(q, x, i, j, q[i] + q[j]);
		sum := q[i] + q[j];
		assert LoopInv(q, x, i, j, sum);
	}

	assert 0 <= i < j < |q| && sum == q[i] + q[j]; // from the loop invariant
	assert sum == x; // from the negation of the loop guard
	// ==>
	assert i < j < |q| && q[i] + q[j] == x;
}
