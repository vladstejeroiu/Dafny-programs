class Global{
  var N_LAS: int;
  var N_PAS: int;
  var N_DIFF: int;
  var las: array<int>;
  var pas: array<int>;
  var l2p_ram: array<int>;
  var l2p_flash: array<int>;
  var p: int;

  predicate init()
  reads this;
  reads las, pas, l2p_ram, l2p_flash;
  requires inv()
  {
    //   N_LAS == 4000000
    //&& N_PAS == 6000000
    //&& N_DIFF == 4000000
    && forall k: int :: 0 <= k < N_DIFF ==> las[k] == 0
    && forall k: int :: 0 <= k < N_DIFF ==> pas[k] == 0
    && forall k: int :: 0 <= k < N_LAS ==> l2p_ram[k] == 0
    && forall k: int :: 0 <= k < N_LAS ==> l2p_flash[k] == 0
  }
  predicate inv()
  reads this;
  {
       N_DIFF == N_LAS
    && 0 <= p < N_DIFF
    && las.Length == N_DIFF
    && pas.Length == N_DIFF
    && l2p_flash.Length == N_LAS
    && l2p_ram.Length == N_LAS
  }
  predicate ri()
  reads this;
  reads las;
  {
    forall i | 0 <= i < p < las.Length ::
                exists lbnd | i <= lbnd <= p < las.Length ::
                         las[i] == las[lbnd]
                      && notin(lbnd, p, las[i], las)
  }

}

method write (global0: Global, la: int, pa: int) returns (global1: Global)
  modifies global0.l2p_ram;
  modifies global0.l2p_flash;
  modifies global0.las;
  modifies global0.pas;
  modifies global0;
  requires global0.inv();
  requires global0.ri();
  requires 0 <= la && 0 <= pa;
  //ensures 0 <= global1.p < global1.N_DIFF
  //ensures la >= global0.N_LAS || pa >= global0.N_PAS ==> global0 == global1;
  //ensures global1.l2p_flash.Length == global1.N_LAS == global1.l2p_ram.Length
  //ensures la < global0.N_LAS && pa < global0.N_PAS ==>
  //  global1.p == global1.N_DIFF - 1 ==> forall k: int :: 0 <= k < global1.N_LAS ==> global1.l2p_flash[k] == global1.l2p_ram[k]
  ensures global1.inv();
  ensures global1.ri();
{
    global1 := global0;
    assert 0 <= global1.p < global1.N_DIFF <= global1.N_LAS;
    assert global1.l2p_flash.Length == global1.N_LAS;
    assert global1.l2p_ram.Length == global1.N_LAS;
    if (la >= global1.N_LAS || la < 0 || pa >= global1.N_PAS || pa < 0)
      {
        return global1;
      }
    assert la < global1.N_LAS && pa < global1.N_PAS;
    global1.l2p_ram[la] := pa;
    global1.las[global1.p] := la;
    assert global1.las[global1.p] == la;
    ghost var lass := global1.las;
    global1.pas[global1.p] := pa;
    assert lass == global1.las;
    assert global1.las[global1.p] == la;
    //assert global1.l2p_ram[global1.las[global1.p]] == pa;
    //assert global1.l2p_ram[global1.las[global1.p]] == global1.pas[global1.p];
    global1.p := global1.p + 1;
    if (global1.p == global1.N_DIFF)
      {
          global1.p := 0;
          var i := 0;
          while (i < global1.N_LAS)
            invariant 0 <= i <= global1.N_LAS
            modifies global1.l2p_flash;
            //invariant forall k: int :: 0 <= k < global1.N_LAS ==> global1.l2p_flash[k] == global1.l2p_ram[k]
          {
              assert i < global1.N_LAS;
              global1.l2p_flash[i] :=  global1.l2p_ram[i];
              i := i + 1;
          }
      }
    //assert global0.p < global0.N_DIFF ==> global1.p == global0.p + 1;
    assert global0.p == global0.N_DIFF ==> global1.p == 0;
    AllRI(global1);
    //assert forall i | 0 <= i < global1.p ::
    //                 exists lbnd | i <= lbnd <= global1.p ::
    //                          global1.las[i] == global1.las[lbnd]
    //                       && notin(lbnd, global1.p, global1.las[i], global1.las);
    return global1;
}

lemma AllRI(global: Global)
  requires global.inv()
  ensures global.ri()
{
  var i := 0;
  var bnd := i + 1;
  RI(global, i);
  while(bnd < global.p)
    //invariant exists lbnd | i <= lbnd <= global.p ::
    //                        global.las[i] == global.las[lbnd]
    //                     && notin(lbnd, global.p, global.las[i], global.las);
    invariant forall i | 0 <= i < bnd ::
                exists lbnd | i <= lbnd <= global.p ::
                         global.las[i] == global.las[lbnd]
                      && notin(lbnd, global.p, global.las[i], global.las);
    invariant i + 1 == bnd;
    invariant i < bnd;
  {
    i   := i + 1;
    bnd := bnd + 1;
    RI(global, i);
  }
//  assert forall i | 0 <= i <= bnd ::
//           exists lbnd | i <= lbnd <= global.p ::
//                    global.las[i] == global.las[lbnd]
//                 && notin(lbnd, global.p, global.las[i], global.las);
}

lemma RI(global: Global, i: int)
  //requires global.init()
  requires global.inv()
  requires 0 <= i <= global.p
  ensures exists lbnd | i <= lbnd <= global.p ::
                      global.las[i] == global.las[lbnd]
                   && notin(lbnd, global.p, global.las[i], global.las);
{
  var lbnd := i;
  var rbnd := i;
  var j := global.p;
  var la := global.las[i];
  while (rbnd < global.p)
    invariant i <= lbnd <= rbnd <= global.p < global.las.Length
    invariant global.las[lbnd] == la
    invariant notin(lbnd, rbnd, la, global.las)
  {
    if (global.las[rbnd] == la)
    {
      lbnd := rbnd;
    }
    rbnd := rbnd + 1;
  }
  //assert rbnd == global.p;
  //assert notin(lbnd, rbnd, la, global.las);
  //assert exists lbnd | i <= lbnd <= global.p < global.las.Length ::
  //                notin(lbnd, global.p, la, global.las);
}

predicate notin(i: int, j: int, la: int, arr: array<int>)
  requires 0 <= i <= j < arr.Length
  reads arr
{
  forall k | i < k < j :: arr[k] != la
}

//lemma RI2(i: int, j: int, la: int, arr: array<int>)
//  requires notin(i, j, la, arr)
//  ensures forall jj :: j <= jj < arr.Length ==> notin(i, jj, la, arr)
//{
//  var i1 := i;
//  while(i1 < j)
//}
