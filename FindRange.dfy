method Main()
{
	var q := [1,2,2,5,10,10,10,23];
	assert Sorted(q);
	assert 10 in q;
	var i,j := FindRange(q, 10);
	print "The number of occurrences of 10 in the sorted sequence [1,2,2,5,10,10,10,23] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j;
	print ").\n";
	assert i == 4 && j == 7 by {
		assert q[0] <= q[1] <= q[2] <= q[3] < 10;
		assert q[4] == q[5] == q[6] == 10;
		assert 10 < q[7];
	}
	
	// arr = [0, 1, 2]       		 key = 10   ->   left = right = |q| = 3
	q := [0,1,2];
	assert Sorted(q);
	i,j := FindRange(q, 10);
	print "The number of occurrences of 10 in the sorted sequence [0,1,2] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j;
	print ").\n";
	
	// arr = [10, 11, 12]    		 key = 1    ->   left = right = 0
	q := [10,11,12];
	assert Sorted(q);
	i,j := FindRange(q, 1);
	print "The number of occurrences of 1  in the sorted sequence [10,11,12] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j;
	print ").\n";
	
	// arr = [1, 11, 22]     		 key = 10   ->   left = right = i+1 = 1     i is the nearest index to key
	q := [1,11,22];
	assert Sorted(q);
	i,j := FindRange(q, 10);
	print "The number of occurrences of 10 in the sorted sequence [1,11,22] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j;
	print ").\n";
	
	// arr = [1 ,11, 22]     		 key = 11   ->   left = 1, right = 2  
	q := [1,11,22];
	assert Sorted(q);
	i,j := FindRange(q, 11);
	print "The number of occurrences of 11 in the sorted sequence [1,11,22] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j;
	print ").\n";
	
	// arr = [1 ,11, 11]     		 key = 11   ->   left = 1, right = 3
	q := [1,11,11];
	assert Sorted(q);
	i,j := FindRange(q, 11);
	print "The number of occurrences of 11 in the sorted sequence [1,11,11] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j;
	print ").\n";
	
	// arr = [11 ,11, 14]     		 key = 11   ->   left = 0, right = 2
	q := [11 ,11, 14];
	assert Sorted(q);
	i,j := FindRange(q, 11);
	print "The number of occurrences of 11 in the sorted sequence [11 ,11, 14] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j;
	print ").\n";
	
	// arr = [1 ,11, 11, 11, 13]     key = 11   ->   left = 1, right = 4
	q := [1,11,11,11,13];
	assert Sorted(q);
	i,j := FindRange(q, 11);
	print "The number of occurrences of 11 in the sorted sequence [1,11,11,11,13] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j;
	print ").\n";
	
	// arr = []     key = 11   ->   left = 0, right = 0
	q := [];
	assert Sorted(q);
	i,j := FindRange(q, 11);
	print "The number of occurrences of 11 in the sorted sequence [] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j;
	print ").\n";
	
	// arr = [11]     key = 10   ->   left = 0, right = 0
	q := [11];
	assert Sorted(q);
	i,j := FindRange(q, 10);
	print "The number of occurrences of 10 in the sorted sequence [11] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j;
	print ").\n";
	
	// arr = [11]     key = 11   ->   left = 0, right = 1
	q := [11];
	assert Sorted(q);
	i,j := FindRange(q, 11);
	print "The number of occurrences of 11 in the sorted sequence [11] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j;
	print ").\n";
}

predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}


method {:verify true} FindRange(q: seq<int>, key: int) returns (left: nat, right: nat)
	requires Sorted(q)
	ensures left <= right <= |q|
	ensures forall i :: 0 <= i < left ==> q[i] < key
	ensures forall i :: left <= i < right ==> q[i] == key
	ensures forall i :: right <= i < |q| ==> q[i] > key
{
	left,right := 0,|q|;
	// all elements in q are greater than key or q is empty
	if(|q| == 0 || q[0] > key){
		left,right := 0,0;
	}
		// all elements in q are less than key
	else if (q[|q|-1] < key){
		left,right := |q|,|q|;
	}
	// key is in q or in the range of number in q
	else
	{
		var low,high := 0,|q|-1;
		var middle:nat := (low+high)/2;
		while (low <= high)
			invariant 0 <= left <= middle < right == |q|;
			invariant -1 <= high <= |q|-1;
			invariant 0 <= low <= |q|;
			invariant forall i :: 0 <= i < low ==> q[i] < key;
			invariant forall i :: high < i < |q| ==> q[i] >= key;
			decreases high-low;
		{
			middle := (low+high)/2;
			if (q[middle] >= key){
				high := middle -1;
			} else{
				low := middle+1;
			}	
		}
		left := high + 1;
		low,high := left,|q|-1;
		middle := (low+high)/2;
		while (low <= high) 
			invariant high >= left - 1;
			invariant 0 <= high <= |q|-1 < right;
			invariant 0 <= low <= |q|;
			invariant forall i :: 0 <= i < low ==> q[i] <= key;
			invariant forall i :: high < i < |q| ==> q[i] > key;
			decreases high-low
		{
			middle:= (low+high)/2;
			if (q[middle] > key){
				high := middle -1;
			}else{
				low := middle + 1;
			}
		}
		right := high + 1;
	}	
}
