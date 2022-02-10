datatype BT<T> = Tip(T) | Node(BT<T>, BT<T>)

class IO<T> {
	var alpha: seq<T>, omega: seq<T>;

	method Input() returns (x: T)
		requires !EOF() // alpha != []
		modifies this
		ensures omega == old(omega)
		ensures old(alpha) == [x] + alpha
	{
		x, alpha := alpha[0], alpha[1..];
	}

	method Output(x: T)
		modifies this
		ensures alpha == old(alpha)
		ensures omega == old(omega) + [x]
	{
		omega := omega + [x];
	}

	method Rewrite()
		modifies this
		ensures omega == []
		ensures alpha == old(alpha)
	{
		omega := [];
	}

	predicate method EOF() reads this { alpha == [] }

}

method Main()
{
	var tree: BT<int>;
	tree := Tip(1);
	var io: IO<int>;
	io := new IO<int>;
	FrontierIter(tree, io);
	print io.omega;

	io.Rewrite();
	tree := Node(tree, Tip(2));
	FrontierIter(tree, io);
	print io.omega;
}

function Frontier<T>(tree: BT<T>): seq<T>
{
	match tree {
		case Tip(n) => [n]
		case Node(left, right) => Frontier(left) + Frontier(right)
	}
}

function Frontiers<T>(trees: seq<BT<T>>): seq<T>
{
	if trees == [] then [] else Frontier(trees[0]) + Frontiers(trees[1..])
}

// TODO: implement iteratively (with a loop),
// updating the value of "io.omega" through calls to "io.Output" for each "tip" of the tree;
// document each proof obligation, as we've learned, with assertion propagation and a lemma
method FrontierIter<T>(tree: BT<T>, io: IO<T>)
	modifies io
	ensures io.omega == old(io.omega) + Frontier(tree)
{
	// The implementation is efficient because each operation of the stack manipulation is O(1).

	var stack : List<BT<T>> := Cons(tree, Empty); // grows towards the beginning
	while stack != Empty
		invariant LoopInv(tree, stack, io.omega, old(io.omega))
		decreases ForestSize(stack)
	{
		ghost var V0 := ForestSize(stack);

		assert stack != Empty;
		assert LoopInv(tree, stack, io.omega, old(io.omega));

		match stack
		{
			case Cons(t, s) =>
			{
				assert stack == Cons(t, s) != Empty;
				assert LoopInv(tree, stack, io.omega, old(io.omega));

				match t
				{
					case Tip(x) =>
					{
						assert stack == Cons(t, s) != Empty;
						assert LoopInv(tree, stack, io.omega, old(io.omega));
						assert t == Tip(x);
						// ==>?
						EnsureInvTip(tree, stack, s, t, x, io.omega, old(io.omega));
						EnsureDecreaseTip(stack, s, t, x);
						assert LoopInv(tree, s, io.omega + [x], old(io.omega));
						assert 0 <= ForestSize(s) < V0;

						io.Output(x);

						assert LoopInv(tree, s, io.omega, old(io.omega));
						assert 0 <= ForestSize(s) < V0;
					}
					case Node(t1, t2) =>
					{
						assert stack == Cons(t, s) != Empty;
						assert LoopInv(tree, stack, io.omega, old(io.omega));
						assert t == Node(t1, t2);
						// ==>?
						EnsureInvNode(tree, stack, s, t, t1, t2, io.omega, old(io.omega));
						EnsureDecreaseNode(stack, s, t, t1, t2);
						assert LoopInv(tree, Cons(t1, Cons(t2, s)), io.omega, old(io.omega));
						assert 0 <= ForestSize(Cons(t1, Cons(t2, s))) < V0;

						s := Cons(t1, Cons(t2, s));

						assert LoopInv(tree, s, io.omega, old(io.omega));
						assert 0 <= ForestSize(s) < V0;
					}
				}

				assert LoopInv(tree, s, io.omega, old(io.omega));
				assert 0 <= ForestSize(s) < V0;
				stack := s;
				assert LoopInv(tree, stack, io.omega, old(io.omega));
				assert 0 <= ForestSize(stack) < V0;
			} // end case Cons()
		} // end match

		assert LoopInv(tree, stack, io.omega, old(io.omega)); // maintaining the loop invariant
		assert 0 <= ForestSize(stack) < V0; // the loop termination
	}

	assert LoopInv(tree, stack, io.omega, old(io.omega)); // from the loop invariant
	assert stack == Empty; // from the negation of the loop guard
	// ==>
	EnsurePostCondition(tree, stack, io.omega, old(io.omega));
	assert io.omega == old(io.omega) + Frontier(tree);
}

datatype List<T> = Empty | Cons(T, List<T>)

function FrontiersList<T>(forest: List<BT<T>>): seq<T>
	decreases forest
{
	match forest
	{
		case Empty => []
		case Cons(tree, forest') => Frontier(tree) + FrontiersList(forest')
	}
}

predicate LoopInv<T>(tree: BT<T>, forest: List<BT<T>>, omega: seq<T>, old_omega: seq<T>)
{
	omega + FrontiersList(forest) == old_omega + Frontier(tree)
}

function TreeSize<T>(tree: BT<T>): nat
	decreases tree
	ensures TreeSize(tree) >= 1
{
	match tree
	{
		case Tip(x) => 1
		case Node(t1, t2) => 1 + TreeSize(t1) + TreeSize(t2)
	}
}

function ForestSize<T>(forest: List<BT<T>>): nat
	decreases forest
	ensures ForestSize(forest) >= 0
{
	match forest
	{
		case Empty => 0
		case Cons(tree, forest') => TreeSize(tree) + ForestSize(forest')
	}
}

lemma EnsureInvTip<T>(tree: BT<T>, stack: List<BT<T>>, s: List<BT<T>>, t: BT<T>, x: T, omega: seq<T>, old_omega: seq<T>)
	requires stack == Cons(t, s)
	requires LoopInv(tree, stack, omega, old_omega)
	requires t == Tip(x)
	
	ensures LoopInv(tree, s, omega + [x], old_omega)
{
}

lemma EnsureDecreaseTip<T>(stack: List<BT<T>>, s: List<BT<T>>, t: BT<T>, x: T)
	requires stack == Cons(t, s)
	requires t == Tip(x)
	
	ensures 0 <= ForestSize(s) < ForestSize(stack)
{
}

lemma EnsureInvNode<T>(tree: BT<T>, stack: List<BT<T>>, s: List<BT<T>>, t: BT<T>, t1: BT<T>, t2: BT<T>, omega: seq<T>, old_omega: seq<T>)
	requires stack == Cons(t, s)
	requires LoopInv(tree, stack, omega, old_omega)
	requires t == Node(t1, t2)
	
	ensures LoopInv(tree, Cons(t1, Cons(t2, s)), omega, old_omega)
{
}

lemma EnsureDecreaseNode<T>(stack: List<BT<T>>, s: List<BT<T>>, t: BT<T>, t1: BT<T>, t2: BT<T>)
	requires stack == Cons(t, s)
	requires t == Node(t1, t2)
	
	ensures 0 <= ForestSize(Cons(t1, Cons(t2, s))) < ForestSize(stack)
{
}

lemma {:induction false} EnsurePostCondition<T>(tree: BT<T>, stack: List<BT<T>>, omega: seq<T>, old_omega: seq<T>)
	requires LoopInv(tree, stack, omega, old_omega)
	requires stack == Empty

	ensures omega == old_omega + Frontier(tree)
{
}

// The cleaner version
method FrontierIter'<T>(tree: BT<T>, io: IO<T>)
	modifies io
	ensures io.omega == old(io.omega) + Frontier(tree)
{
	var stack : List<BT<T>> := Cons(tree, Empty); // grows towards the beginning
	while stack != Empty
		invariant LoopInv(tree, stack, io.omega, old(io.omega))
		decreases ForestSize(stack)
	{
		ghost var V0 := ForestSize(stack);

		match stack
		{
			case Cons(t, s) =>
			{
				match t
				{
					case Tip(x) =>
					{
						io.Output(x);
					}
					case Node(t1, t2) =>
					{
						s := Cons(t1, Cons(t2, s));
					}
				}

				stack := s;
			}
		}

		assert 0 <= ForestSize(stack) < V0; // the loop termination
	}
}
