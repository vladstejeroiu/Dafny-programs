include "AvlNode.dfy"

class AvlTree {
    ghost var Contents: set<int>
    ghost var Repr: set<object>

    var root: AvlNode?;

    predicate Valid()
        reads this, Repr
    {
        this in Repr &&
        (root == null ==> Contents == {}) &&
        (root != null ==>
            root in Repr && root.Repr <= Repr &&
            root.Valid() &&
            Contents == root.Contents)
    }

    predicate Balanced()
        reads this, Repr
    {
        Valid() &&
        (root != null ==> root.Balanced())
    }

    constructor Init()
        ensures Valid() && fresh(Repr - {this})
        ensures Contents == {}
        ensures Balanced()
    {
        root := null;
        Repr := {this};
        Contents := {};
    }

    method Insert(val: int)
        requires Valid();
        modifies Repr;
        ensures Valid() && fresh(Repr - old(Repr));
        ensures Balanced();
        ensures Contents == old(Contents) + {val};
    {
        print("\n--Inserting ");
        print(val);
        print("\n");
        root := insert_helper(root, val);
        assert root.Valid();
        Contents := root.Contents;
        Repr := root.Repr + {this};
    }

    function method Find(val: int): bool
        requires Valid()
        requires Balanced()
        reads Repr
        ensures Find(val) <==> val in Contents
    {
        root != null && find_helper(val, root)
    }

    function method find_helper(val: int, node:AvlNode): bool
        requires node.Valid()
        reads node.Repr
        ensures find_helper(val, node) <==> val in node.Contents
        decreases node.Repr
    {
        if val == node.data then
        true
        else if node.left != null && val < node.data then
        find_helper(val, node.left)
        else if node.right != null && node.data < val then
        find_helper(val, node.right)
        else
        false
    }

    static function method max(a: int, b: int) : int
    {
        if (a > b) then
            a
        else 
            b
    }

    static method get_height(node:AvlNode?) returns (height:int) {
        if(node == null) {
            height := -1;
        } else {
            height := node.height;
        }
    }

    static method update_height(node:AvlNode)
        modifies node;
        requires node.Valid();
        ensures old(node.left) == node.left;
        ensures old(node.right) == node.right;
        ensures old(node.data) == node.data;
        ensures old(node.Repr) == node.Repr;
        ensures old(node.Contents) == node.Contents;
        ensures node.Valid();
        ensures node.Height_Valid();
    {
        var r:int := get_height(node.right);
        var l:int := get_height(node.left);
        node.height := 1 + max(r,l);
    }

    static method rotate_left(node:AvlNode) returns(new_node:AvlNode)
        requires node.right != null;
        requires node.Valid()
        modifies node.Repr;
        ensures old(node.Repr) == new_node.Repr;
        ensures old(node.Contents) == new_node.Contents;
        ensures new_node.Valid();
        ensures new_node.Height_Valid();
        ensures node.Valid();
        ensures new_node == old(node.right);
        ensures new_node.right == old(new_node.right);
        ensures new_node.left == old(node);
        ensures node.right == old(node.right.left);
        ensures node.left == old(node.left);
    {
        new_node := node.right;
        var T2 := new_node.left;
        new_node.left := node;
        node.Repr := node.Repr - node.right.Repr;
        node.Contents := node.Contents - node.right.Contents;
        node.right := T2;
        if node.right != null {
            node.Repr := node.Repr + node.right.Repr + {node.right};
            node.Contents := node.Contents + node.right.Contents + {node.data};
        }
        if new_node.left != null {
            new_node.Repr := new_node.Repr + new_node.left.Repr + {new_node.left};
            new_node.Contents := new_node.Contents + new_node.left.Contents + {new_node.data};
        }
        update_height(node);
        update_height(new_node);
    }

    
    static method rotate_right(node:AvlNode) returns(new_node:AvlNode)
        requires node.left != null;
        requires node.Valid();
        modifies node.Repr;
        ensures old(node.Repr) == new_node.Repr;
        ensures old(node.Contents) == new_node.Contents;
        ensures new_node.Valid();
        ensures node.Valid();
        ensures new_node.Height_Valid();
        ensures new_node == old(node.left);
        ensures new_node.left == old(new_node.left);
        ensures new_node.right == old(node);
        ensures node.left == old(node.left.right);
        ensures node.right == old(node.right);

    {
        new_node := node.left;
        var T2 := new_node.right;
        new_node.right := node;
        node.Repr := node.Repr - node.left.Repr;
        node.Contents := node.Contents - node.left.Contents;
        node.left := T2;

        if node.left != null {
            node.Repr := node.Repr + node.left.Repr + {node.left};
            node.Contents := node.Contents + node.left.Contents + {node.data};
        }
        if new_node.right != null {
            new_node.Repr := new_node.Repr + new_node.right.Repr + {new_node.right};
            new_node.Contents := new_node.Contents + new_node.right.Contents + {new_node.data};
        }
        update_height(node);
        update_height(new_node);
    }

    static method check_rotation_right(node:AvlNode) returns (new_node:AvlNode)
        modifies node.Repr
        requires node.Valid()
        ensures new_node.Valid()
        ensures new_node.Height_Valid()
        ensures new_node.Balanced()
        ensures node.Valid()
        ensures old(node.Repr) == new_node.Repr;
        ensures old(node.Contents) == new_node.Contents;
        ensures new_node.right != null ==> new_node.right in new_node.right.Repr;
        ensures new_node.left != null ==> new_node.left in new_node.left.Repr;
    {
        print(":r");
        print(node.data);
        new_node := node;
        if node.left != null {
            var r:int := get_height(node.right);
            print(",R=");
            print(r);
            var l:int :=  get_height(node.left);
            print(",L=");
            print(l);
            var diff:int := l-r;
            if diff > 1 {
                var l_r:int := get_height(node.left.right);
                var l_l:int := get_height(node.left.left);
                if l_r > l_l 
                    && new_node.left != null 
                    && new_node.left.right != null 
                {   
                    new_node.left := rotate_left(new_node.left);
                    new_node := rotate_right(new_node);
                    print("dr;");
                }
                else {
                    new_node := rotate_right(new_node);
                    print("r;");
                }
            }
        }
        assert new_node.right != null ==> new_node.right in new_node.right.Repr;
        assert new_node.left != null ==> new_node.left in new_node.left.Repr;
    }

    static method check_rotation_left(node:AvlNode) returns (new_node:AvlNode)
        modifies node.Repr;
        requires node.Valid();
        ensures new_node.Valid();
        ensures new_node.Height_Valid();
        ensures new_node.Balanced()
        ensures node.Valid();
        ensures old(node.Repr) == new_node.Repr;
        ensures old(node.Contents) == new_node.Contents;
        ensures new_node.right != null ==> new_node.right in new_node.right.Repr;
        ensures new_node.left != null ==> new_node.left in new_node.left.Repr;
    {
        print(":l");
        print(node.data);
        new_node := node;
        if new_node.right != null {
            var r:int := get_height(new_node.right);
            print(",R=");
            print(r);
            var l:int :=  get_height(new_node.left);
            print(",L=");
            print(l);
            var diff:int := r-l;
            if diff > 1 {
                var r_r:int := get_height(new_node.right.right);
                var r_l:int := get_height(new_node.right.left);
                if r_l > r_r 
                    && new_node.right != null 
                    && new_node.right.left != null 
                {
                    new_node.right := rotate_right(new_node.right);
                    new_node := rotate_left(new_node);
                    print("dr;");
                }
                else {
                    new_node := rotate_left(new_node);
                    print("r;");
                }
            } 
        }
    }

    
    static method insert_helper(node:AvlNode?, x:int) returns (new_node:AvlNode)
        requires node == null || (node.Valid() && node.Balanced())
        modifies if node != null then node.Repr + {node} else {}
        ensures new_node.Valid()
        ensures new_node.Height_Valid()
        ensures new_node.Balanced()
        ensures node == null ==> fresh(new_node.Repr) && new_node.Contents == {x}
        ensures node != null ==> new_node.Contents == old(node.Contents) + {x}
        ensures node != null ==> fresh(new_node.Repr - old(node.Repr))
        decreases if node == null then {} else node.Repr
    {
        if node == null {
            new_node := new AvlNode.Init(x);
        } else if x == node.data {
            new_node := node;
        } else {
            if x < node.data {
                assert node.right == null || node.right.Valid();
                var t := insert_helper(node.left, x);
                update_height(t);
                node.left := t;
                node.Repr := node.Repr + node.left.Repr;
                node.Contents := node.Contents + {x};
                new_node := node;
                new_node := check_rotation_right(new_node);
            } else {
                assert node.left == null || node.left.Valid();
                var t := insert_helper(node.right, x);
                update_height(t);
                node.right := t;
                node.Repr := node.Repr + node.right.Repr;
                node.Contents := node.Contents + {x};
                new_node := node;
                new_node := check_rotation_left(new_node);
            }
        }
    }

    method Print()
        requires root != null ==> root.Valid();
    {
        print("\n----Tree>>>>");
        print_tree_recursive(root, 3);
        print("<<<<Tree----");
    }

    static method print_tree_recursive(node:AvlNode?, space:int)
        requires node == null || (node.Valid() && node.Balanced())
        decreases if node == null then {} else node.Repr
    {
        var count:int := 5;
        if(node != null) {
            var new_space := space + count;
            print_tree_recursive(node.right, new_space);
            print("\n");
            var i:int := count;
            while(i < new_space)
                decreases new_space - i;
            {
                print(" ");
                i := i + 1;
            }
            print(node.data);
            var r:int := get_height(node.right);
            var l:int :=  get_height(node.left);
            var diff:int := l-r;
            print("(");
            print(diff);
            print(")\n");
            print_tree_recursive(node.left, new_space);
        }
    }

    method Remove(val: int)
        requires Valid()
        requires Balanced()
        modifies Repr
        ensures Valid() && Balanced() && fresh(Repr - old(Repr))
        ensures Contents == old(Contents) - {val}
    {
        print("\n--Removing ");
        print(val);
        print("\n");
        if root != null {
            var newRoot := remove_helper(val, root);
            root := newRoot;
            if root == null {
                Contents := {};
                Repr := {this};
            } else {
                Contents := root.Contents;
                Repr := root.Repr + {this};
            }
        }
    }

    method remove_helper(x: int, node:AvlNode) returns (new_node: AvlNode?)
        requires node.Valid()
        requires node.Balanced()
        modifies node.Repr
        ensures new_node != null ==> fresh(new_node.Repr - old(node.Repr))
        ensures new_node != null ==> new_node.Valid()
        ensures new_node != null ==> new_node.Height_Valid()
        ensures new_node != null ==> new_node.Balanced()
        ensures new_node == null ==> old(node.Contents) <= {x}
        ensures new_node != null ==> new_node.Contents == old(node.Contents) - {x}
        decreases node.Repr
    {
        new_node := node;
        if new_node.left != null && x < new_node.data {
            var t := remove_helper(x, new_node.left);
            new_node.left := t;
            new_node.Contents := new_node.Contents - {x};
            if new_node.left != null { new_node.Repr := new_node.Repr + new_node.left.Repr; }
            update_height(new_node);
            new_node := check_rotation_left(new_node);
        } else if new_node.right != null && new_node.data < x {
            var t := remove_helper(x, new_node.right);
            new_node.right := t;
            new_node.Contents := new_node.Contents - {x};
            if new_node.right != null { new_node.Repr := new_node.Repr + new_node.right.Repr; }
            update_height(new_node);
            new_node := check_rotation_right(new_node);
        } else if x == new_node.data {
            if new_node.left == null && new_node.right == null {
                new_node := null;
            } else if new_node.left == null {
                new_node := new_node.right;
            } else if new_node.right == null {
                new_node := new_node.left;
            } else {
                // rotate
                var min, r := remove_min(new_node.right);
                new_node.data := min;  new_node.right := r;
                new_node.Contents := new_node.Contents - {x};
                if new_node.right != null { new_node.Repr := new_node.Repr + new_node.right.Repr; }
            }
            if (new_node != null) {
                update_height(new_node);
                new_node := check_rotation_left(new_node);
                new_node := check_rotation_right(new_node);
            }
        }
    }

    method remove_min(node: AvlNode) returns (min: int, new_node: AvlNode?)
        requires node.Valid()
        modifies node.Repr
        ensures new_node != null ==> fresh(new_node.Repr - old(node.Repr))
        ensures new_node != null ==> new_node.Valid()
        ensures new_node == null ==> old(node.Contents) == {min}
        ensures new_node != null ==> new_node.Repr <= old(node.Repr)
        ensures new_node != null ==> new_node.Contents == old(node.Contents) - {min}
        ensures min in old(node.Contents) && (forall x :: x in old(node.Contents) ==> min <= x)
        decreases node.Repr
    {
        if node.left == null {
            min := node.data;
            new_node := node.right;
        } else {
            var t;
            min, t := remove_min(node.left);
            node.left := t;
            new_node := node;
            node.Contents := node.Contents - {min};
            if node.left != null { node.Repr := node.Repr + node.left.Repr; }
            if(new_node != null) {
                new_node := check_rotation_left(new_node);
                update_height(new_node);
            }
        }
    }
}