

// A LIFO queue (aka a stack) with limited capacity in Dafny.
class LimitedStack {

      var capacity : int; // capacity, max number of elements allowed on the stack.
      var arr : array<int>; // contents of stack.
      var top : int; // The index of the top of the stack, or -1 if the stack is empty

      // This predicate express a class invariant: All objects of this calls should satisfy this.
      predicate Valid()
      reads this;
      {
        arr != null && capacity > 0 && capacity < arr.Length && -1 <= top < capacity
      }

      predicate Empty()
      reads this;
      {
        top == -1
      }


      predicate Full()
      reads this;
      {
       top == capacity 
      }
      
      method Init(c : int)
      modifies this;
      requires c > 0; 
      ensures fresh(arr);// ensures arr is a newly created object.
      ensures this.arr.Length == c;
      ensures Empty();
      ensures capacity == c && top == -1;
      {
        capacity := c;
        arr := new int[c];
        top := -1;
      }


      
      method isEmpty() returns (res : bool)
      requires Empty() && Valid()
      ensures Empty()
      {
            return true;
      }



      // Returns the top element of the stack, without removing it.
      method Peek() returns (elem : int)
      requires Valid() && !Empty()
      ensures arr == old(arr) && elem == arr[top]
      {
        return arr[top];
      }



      // Pushed an element to the top of a (non full) stack. 
      method Push(elem : int)
      modifies `arr, `top
      requires Valid() && !Full()
      ensures elem == arr[top]
      {
        top := top+1;
        arr[top] := elem;
      }

      // Pops the top element off the stack.
/*  
      method Pop() returns (elem : int)
      
      {
        
      }
 */

/*
      //Push onto full stack, oldest element is discarded.
      method Push2(elem : int)
      
      {
        
      }
*/

/*

// When you are finished,  all the below assertions should be provable. 
// Feel free to add extra ones as well.
      method Main(){
           var s := new LimitedStack;
           s.Init(3);

           assert s.Empty() && !s.Full(); 

           s.Push(27);
           assert !s.Empty();

           var e := s.Pop();
           assert e == 27;

           s.Push(5);
           s.Push(32);
           s.Push(9);
           assert s.Full();

           var e2 := s.Pop();
           assert e2 == 9 && !s.Full(); 
           assert s.arr[0] == 5;

           s.Push(e2);
           s.Push2(99);

           var e3 := s.Peek();
           assert e3 == 99;
           assert s.arr[0] == 32;
                     
       }
*/
}