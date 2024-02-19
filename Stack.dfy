class Node<T> {

    ghost var s: seq<T>
    ghost var Repr: set<object>
    var value: T
    var next: Node?<T>

    predicate Valid()
        reads this, Repr
        ensures Valid() ==> this in Repr
        decreases Repr
    {
        this in Repr &&
        (next == null ==> Repr == {this} && s == [value]) &&
        (next != null ==> next in Repr && next.Repr <= Repr &&
            this !in next.Repr && next.Valid() && s == [value] + next.s)
    }

    constructor (v: T)
        ensures Valid() && fresh(Repr)
        ensures s == [v]
    {
        value := v;
        next := null;
        s := [v];
        Repr := {this};
    }

    method SetNext(n: Node<T>)
        modifies Repr
        requires Valid() && n.Valid()
        requires this !in n.Repr
        ensures Valid() && fresh(Repr - old(Repr) - old(n.Repr))
        ensures s == [value] + n.s
    {
        next := n;
        Repr := Repr + n.Repr;
        s := [value] + n.s;
    }

    method GetValue() returns (v: T)
        requires Valid()
        ensures Valid() && v == s[0]
    {
        v := value;
    }

    method GetNext() returns (n: Node?<T>)
        requires Valid()
        ensures Valid() && n == next
    {
        n := next;
    }
}

class Stack<T> {

    ghost var s: seq<T>
    ghost var Repr: set<object>
    var top: Node?<T>;

    predicate Valid()
        reads this, Repr
        ensures Valid() ==> this in Repr
        decreases Repr
    {
        this in Repr &&
        (|s| == 0 ==> top == null) &&
        (|s| != 0 ==> top in Repr && top.Repr <= Repr &&
            this !in top.Repr && top.Valid() && top.s == s)
    }

    constructor () 
        ensures Valid() && fresh(Repr)
    {
        top := null;
        s := [];
        Repr := {this};
    }

    method IsEmpty() returns (r: bool)
        requires Valid()
        ensures (|s| == 0 ==> r == true) && (|s| > 0 ==> r == false)
    {
        r := top == null;
    }

    method Push(v: T) 
        modifies Repr
        requires Valid()
        ensures Valid() && fresh(Repr - old(Repr))
        ensures (old(top) == null ==> s == [v]) && (old(top) != null ==> s == [v] + old(top).s)
    {
        var newNode := new Node(v);
        if top != null {
            assert newNode.value == v;
            newNode.SetNext(top);
            assert newNode.value != v;
        }
        top := newNode;
        Repr := Repr + top.Repr;
        s := top.s;
    }

    method Pop() returns (v: T)
        modifies Repr
        requires Valid() && top != null
        ensures Valid() && fresh(Repr - old(Repr))
        ensures v == old(s)[0] && s == old(s)[1..]
    {
        v := top.GetValue();
        top := top.GetNext();
        Repr := Repr - {old(top)};
        s := s[1..];
    }
}