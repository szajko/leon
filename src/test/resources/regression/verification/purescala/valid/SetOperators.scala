import leon.Annotations._
import leon.Utils._

object TestCase {

/*  def soSimpleUNSAT(A : Set[Int]) : Boolean = {
    require(A == Set.empty[Int])
    A.size == 0
  } holds 

  def prob1SAT(A : Set[Int], B : Set[Int], C: Set[Int]) : Boolean = {
    !(
      (A ++ B).size <= (B ++ C).size
    )
  } holds
  
  // | A | + | B | <= | A U B | + | A Intersec B |
  def prob2SAT(A : Set[Int], B : Set[Int]) : Boolean = {
    !(
      A.size + B.size <= (A ++ B).size + (A & B).size      
    )
  } holds
  
  //|(A Intersec B)| = |A U B| ^ |A| = 5 ^ | EmptySet |=0
  def prob3SAT(A : Set[Int], B : Set[Int]) : Boolean = {
    !(
      (A & B).size <= (A ++ B).size  && A.size == 5 && Set.empty[Int].size == 0
    )
  } holds
  
   // { 1, 2*2, 3) = { 3-2, 4, x }
  def prob4SAT(x : Int) : Boolean = {
    !(
      Set(1, 2*2, 3) == Set(3-2, 4, x)
    )
  } holds
  
  //| EmptySet | = 1
  def prob1UNSAT() : Boolean = {
    !(
      Set.empty[Int].size == 1
    )
  } holds 
  
  // | A | + | B | != | A U B | + | A Intersec B |
  def prob2UNSAT(A : Set[Int], B : Set[Int]) : Boolean = {
    (A.size + B.size == (A ++ B).size + (A & B).size)
  } holds
  
  //|A|=1 ^ |B|=1 ^ |C|=1 ^ |A Intersec B|=1 ^ |A Intersec C|=1 ^ |B Intersec C|=0
  def prob3UNSAT(A : Set[Int], B : Set[Int], C: Set[Int]) : Boolean = {
    !(
      A.size == 1 && B.size == 1 && C.size == 1 && (A & B).size == 1 && (A & C).size == 1 && (B & C).size == 0
    )
  } holds
  
  
  // |A| != 0 ^ A = Set()
  def prob4UNSAT(A : Set[Int]) : Boolean = {
    (A.size == 0 || A != Set.empty[Int])
  } holds
 
  //|A| != 0 => A = Set()) ^ (A = Set() => |A| != 0)
  def vc1UNSAT(A : Set[Int]) : Boolean = {
    //!(
    //  (A.size == 0 || A == Set.empty[Int]) && ( A != Set.empty[Int] || A.size != 0)         
    //)
    ((A.size != 0 && A != Set.empty[Int]) || ( A == Set.empty[Int] && A.size == 0))
  } holds 
  
  //!(x16 in S17) ^ |S17  U Set(x16)|!=(|S17| + 1)
  def vc2UNSAT(x16: Int, S17 : Set[Int], B : Set[Int]) : Boolean = {
    //!(
    //   !S17.contains(x16) && (S17 ++ Set(x16)).size != S17.size +1
    //)
    (S17.contains(x16) || (S17 ++ Set(x16)).size == S17.size +1 )
  } holds
  
  //x16 in S17 ^ !(x18 in S19) ^  S19 subseteq S20^(x18 in S21)^(x18 in S20) ^ |S19  U Set(x18)| != |S19|+1
  def vc2aUNSAT(x16: Int, x18: Int, S17: Set[Int], S19: Set[Int], S20: Set[Int], S21: Set[Int]) : Boolean = {
    !(
      S17.contains(x16) && !S19.contains(x18) && S19.subsetOf(S20) && S21.contains(x18) && 
        S20.contains(x18) && (S19 ++ Set(x18)).size != S19.size + 1
    )
  } holds
  
  //l16 in L17 ^ S18 subseteq O19 ^  x20 in OB21 ^ x20 in O19 ^ |S18 U Set(x20)| != |S18| + 1
  def vc2bSAT(l16: Int, x20: Int, L17: Set[Int], O19: Set[Int], OB21: Set[Int], S18: Set[Int]) : Boolean = {
    !(
      L17.contains(l16) &&  S18.subsetOf(O19) && OB21.contains(x20) && O19.contains(x20) && 
        (S18 ++ Set(x20)).size != S18.size + 1
    )
  } holds
  
  //| S16 U Set(x17)| > |S16| + 1
  def vc3UNSAT(x17: Int, S16: Set[Int]) : Boolean = {
    ((S16 ++ Set(x17)).size <= S16.size + 1)
  } holds
  
  //S16 subseteq A17 ^ a18 in A17 ^ b19 in A17 ^|S16 U Set(x20)| > |S16| + 1
  def vc3aUNSAT(a18: Int, b19: Int, x20: Int, S16: Set[Int], A17: Set[Int]) : Boolean = {
    !(
      S16.subsetOf(A17) && A17.contains(a18) && A17.contains(b19) && 
        (S16 ++ Set(x20)).size > S16.size + 1
    )
  } holds
  
  //S16 subseteq A17 ^ a18 in A17 ^ b19 in A17 ^ |S16 U Set(x20)| != |S16| + 1
  def vc3bSAT(a18: Int, b19: Int, x20: Int, S16: Set[Int], A17: Set[Int]) : Boolean = {
    !(
      S16.subsetOf(A17) && A17.contains(a18) && A17.contains(b19) && 
        (S16 ++ Set(x20)).size != S16.size + 1
    )
  } holds
  
  //C16 subseteq A17 ^ !( x118 in A17) ^  !(x219 in A17 U Set(x118)) ^!(  x320 in A17 U Set(x118) U Set(x219)) ^ 
  //|C16 U Set(x118) U Set(x219) U Set(x320)| != |C16| + 3 
  def vc4UNSAT(x118: Int, x219: Int, x320: Int, C16: Set[Int], A17: Set[Int]) : Boolean = {
    !(
      C16.subsetOf(A17) && !A17.contains(x118) && ! (A17 ++ Set(x118)).contains(x219) && 
        !(A17 ++ Set(x118) ++ Set(x219)).contains(x320) && 
        (C16 ++ Set(x118) ++ Set(x219) ++ Set(x320)).size != C16.size + 3
    )
  } holds
  
  //C16 subseteq A17 ^  !(x118 in A17) ^ !( x219 in A17) ^  
  //!(x320 in A17 U Set(x118) U Set(x219)) ^ | C16 U Set(x118) U Set(x219) U Set(x320)| !=|C16| + 3
  def vc4bSAT(x118: Int, x219: Int, x320: Int, C16: Set[Int], A17: Set[Int]) : Boolean = {
    !(
      C16.subsetOf(A17) && !A17.contains(x118) && ! A17.contains(x219) && 
        !(A17 ++ Set(x118) ++ Set(x219)).contains(x320) && 
        (C16 ++ Set(x118) ++ Set(x219) ++ Set(x320)).size != C16.size + 3
    )
  } holds
  
  //C16 subseteq AL17 ^ ! x118 in AL17 ^  AL17 U Set(x118) subseteq AL19 ^  ! x220 in AL19 ^ 
  //AL19 U Set(x220) subseteq AL221 ^  ! x322 in AL221 ^| C16 U Set(x118) U Set(x220) U Set(x322)| != |C16| + 3
  def vc5UNSAT(x118: Int, x220: Int, x322: Int, C16: Set[Int], AL17: Set[Int], AL19: Set[Int], AL221: Set[Int]) : Boolean = {
    !(
      C16.subsetOf(AL17) && !AL17.contains(x118) &&  (AL17 ++ Set(x118)).subsetOf(AL19) && 
        ! AL19.contains(x220) && (AL19 ++ Set(x220)).subsetOf(AL221) && ! AL221.contains(x322) &&
        (C16 ++ Set(x118) ++ Set(x220) ++ Set(x322)).size != C16.size + 3
    )
  } holds
  

  //C16 subseteq AL17 ^ AL17 U Set(x118) subseteq AL19 ^  ! x220 in AL19 ^  AL19 U Set(x220) subseteq AL221 ^ 
  //! x322 in AL221 ^| C16 U Set(x118) U Set(x220) U Set(x322)| != |C16| + 3
  def vc5bSAT(x118: Int, x220: Int, x322: Int, C16: Set[Int], AL17: Set[Int], AL19: Set[Int], AL221: Set[Int]) : Boolean = {
    !(
      C16.subsetOf(AL17) && (AL17 ++ Set(x118)).subsetOf(AL19) && 
        ! AL19.contains(x220) && (AL19 ++ Set(x220)).subsetOf(AL221) && ! AL221.contains(x322) &&
        (C16 ++ Set(x118) ++ Set(x220) ++ Set(x322)).size != C16.size + 3
    )
  } holds
  
  //x16 in C17 ^ C18 = C17 Intersec Compl(Set(x16)) ^ |AL19 Intersec Compl(AL20)| <= 1 ^ 
  //|AL221 Intersec Compl(AL19)| <= |C18| ^ |AL221 Intersec Compl(AL20)| > |C17|
  def vc6UNSAT(x16: Int, C17: Set[Int], C18: Set[Int], AL19: Set[Int], AL20: Set[Int], AL221: Set[Int]) : Boolean = {
    !(
      C17.contains(x16) && C18 == C17 -- Set(x16) && (AL19 -- AL20).size == 1 && 
      (AL221 -- AL19).size <= C18.size  && (AL221 -- AL20).size > C17.size 
      )
  } holds 
  
  //l116 != nul17 ^ l116 != ths18 ^ ths18 != nul17 ^ ths18 in L19 ^ ths18 in OC20 ^ l116 in L19 ^ 
  //l116 in OC20 ^ Oc7421 = OC20 ^ L7322 = S23 ^ OC20 subseteq Oc7421 ^ Oc6025 = Oc7421 ^ ListContent5926 = L7322 ^ 
  //Oc7421 subseteq Oc6025 ^ tmp35727 in OB28 ^ tmp35727 in Oc6025 ^ Oc4529 = Oc6025 ^ Oc6025 subseteq Oc4529 ^ 
  //Oc4529 = OC20 ^ tmp35727 in S14230 ^ S24131 = S14230 Intersec Compl(Set(tmp35727)) ^
  //| Oc3032 Intersec Compl(Oc4529) |<= 1^ Oc4529 subseteq Oc3032 ^ |Oc3032 Intersec Compl(OC20)|<=1
  //^ Oc3032 subseteq Oc1633 ^| Oc1633  Intersec Compl(Oc3032)|<=|S24131|^ |Oc1633 Intersec Compl(OC20)|> |S14230| 
  def vc6aUNSAT(l116: Int, nul17: Int, ths18: Int, tmp35727: Int, L19: Set[Int], OC20: Set[Int], OB28: Set[Int] , Oc7421: Set[Int], L7322: Set[Int], S23: Set[Int], Oc6025: Set[Int], ListContent5926: Set[Int], Oc4529: Set[Int], S24131: Set[Int], Oc3032: Set[Int], Oc1633: Set[Int], S14230: Set[Int] ) : Boolean = {
    !(
      l116!= nul17 && l116 != ths18 && ths18 != nul17 && L19.contains(ths18) && OC20.contains(ths18) &&
      L19.contains(l116) && OC20.contains(l116) && Oc7421 == OC20 && L7322 == S23 && OC20.subsetOf(Oc7421) &&
      Oc6025 == Oc7421 && ListContent5926 == L7322 && Oc7421.subsetOf(Oc6025) && OB28.contains(tmp35727) &&
      Oc6025.contains(tmp35727) && Oc4529 == Oc6025 && Oc6025.subsetOf(Oc4529) && Oc4529 == OC20 &&
      S14230.contains(tmp35727) && S24131 == S14230 -- Set(tmp35727) && (Oc3032 -- Oc4529).size <= 1 &&
      Oc4529.subsetOf(Oc3032) && (Oc3032 -- OC20).size <= 1 && Oc3032.subsetOf(Oc1633) &&
      (Oc1633 -- Oc3032).size <= S24131.size && (Oc1633 -- OC20).size > S14230.size 
    )
  } holds
  
  //l116 != nul17 ^ l116 != ths18 ^ ths18 != nul17 ^ ths18 in L19 ^ ths18 in OC20 ^ 
  //l116 in L19 ^ l116 in OC20 ^ Oc7421 = OC20^ L7322 = S23 ^ OC20 subseteq Oc7421 ^ 
  //Oc6025 = Oc7421 ^ ListContent5926  = L7322 ^ Oc7421 subseteq Oc6025 ^ tmp35727 in OB28 ^ 
  //tmp35727 in Oc6025 ^ Oc4529 = Oc6025 ^ Oc6025 subseteq Oc4529^ Oc4529 = OC20 ^ 
  //tmp35727 in S14230 ^ S24131 = S14230 Intersec Compl( Set(tmp35727)) ^ | Oc3032 Intersec Compl(Oc4529)| <= 1 ^ 
  //Oc4529 subseteq Oc3032 ^ | Oc3032 Intersec Compl(OC20)| <= 1 ^ Oc3032 subseteq Oc1633 ^ 
  //| Oc1633 Intersec Compl(Oc3032) | <= |S24131| ^ | Oc1633 Intersec Compl(OC20)| >= |S14230| 
  def vc6bSAT(l116: Int, nul17: Int, ths18: Int, tmp35727: Int, L19: Set[Int], OC20: Set[Int], OB28: Set[Int] , Oc7421: Set[Int], L7322: Set[Int], S23: Set[Int], Oc6025: Set[Int], ListContent5926: Set[Int], Oc4529: Set[Int], S24131: Set[Int], Oc3032: Set[Int], Oc1633: Set[Int], S14230: Set[Int] ) : Boolean = {
    !(
      l116!= nul17 && l116 != ths18 && ths18 != nul17 && L19.contains(ths18) && OC20.contains(ths18) &&
      L19.contains(l116) && OC20.contains(l116) && Oc7421 == OC20 && L7322 == S23 && OC20.subsetOf(Oc7421) &&
      Oc6025 == Oc7421 && ListContent5926 == L7322 && Oc7421.subsetOf(Oc6025) && OB28.contains(tmp35727) &&
      Oc6025.contains(tmp35727) && Oc4529 == Oc6025 && Oc6025.subsetOf(Oc4529) && Oc4529 == OC20 &&
      S14230.contains(tmp35727) && S24131 == S14230 -- Set(tmp35727) && (Oc3032 -- Oc4529).size <= 1 &&
      Oc4529.subsetOf(Oc3032) && (Oc3032 -- OC20).size <= 1 && Oc3032.subsetOf(Oc1633) &&
      (Oc1633 -- Oc3032).size <= S24131.size && (Oc1633 -- OC20).size >= S14230.size 
    )
  } holds
  
  //l116 != nul17 ^ l116 != ths18 ^ ths18 != nul17 ^ ths18 in L19 ^ ths18 in OC20 ^ 
  //l116 in L19 ^ l116 in OC20 ^ Oc7421 = OC20 ^ L7322 = S23 ^ OC20 subseteq Oc7421 ^ 
  //Oc6025 = Oc7421 ^ ListContent5926 = L7322 ^ Oc7421 subseteq Oc6025 ^ tmp35727 in OB28 ^ 
  //tmp35727 in Oc6025 ^ Oc4529 = Oc6025 ^ Oc6025 subseteq Oc4529 ^  Oc4529  = OC20 ^ 
  
  //S24130 = S14231 Intersec Compl(Set(tmp35727)) ^ |Oc3032 Intersec Compl(Oc4529)| <= 1 ^ 
  //Oc4529 subseteq Oc3032 ^ |Oc3032 Intersec Compl(OC20)| <= 1 ^ Oc3032 subseteq Oc1633 ^ 
  //|Oc1633 Intersec Compl(Oc3032) | <= |S24130| ^ | Oc1633 Intersec Compl(OC20)| > |S14231|
  def vc6cSAT(l116: Int, nul17: Int, ths18: Int, tmp35727: Int, L19: Set[Int], OC20: Set[Int], OB28: Set[Int] , Oc7421: Set[Int], L7322: Set[Int], S23: Set[Int], Oc6025: Set[Int], ListContent5926: Set[Int], Oc4529: Set[Int], S24130: Set[Int], S24131: Set[Int], S14231: Set[Int] , Oc3032: Set[Int], Oc1633: Set[Int], S14230: Set[Int] ) : Boolean = {
    !(
      l116!= nul17 && l116 != ths18 && ths18 != nul17 && L19.contains(ths18) && OC20.contains(ths18) &&
      L19.contains(l116) && OC20.contains(l116) && Oc7421 == OC20 && L7322 == S23 && OC20.subsetOf(Oc7421) &&
      Oc6025 == Oc7421 && ListContent5926 == L7322 && Oc7421.subsetOf(Oc6025) && OB28.contains(tmp35727) &&
      Oc6025.contains(tmp35727) && Oc4529 == Oc6025 && Oc6025.subsetOf(Oc4529) && Oc4529 == OC20 &&
      S24130 == S14231 -- Set(tmp35727) && (Oc3032 -- Oc4529).size <= 1 &&
      Oc4529.subsetOf(Oc3032) && (Oc3032 -- OC20).size <= 1 && Oc3032.subsetOf(Oc1633) &&
      (Oc1633 -- Oc3032).size <= S24130.size && (Oc1633 -- OC20).size > S14230.size 
    )
  } holds */
  
  //Test the program with formulas containing min-max constraints
  
/*  //empty set are solution
  //Min(A \ B) = Min(B \ A) ^ |A U B| = 2
  def mProb1SAT(A: Set[Int], B: Set[Int]) : Boolean = {
    !(
      (A -- B).min == (B -- A).min && (A ++ B).size == 2
    )
  } holds

  
  //min-max values are in the same cluster
  //Min(A \ B) = Min(B \ A) ^ |A \ B| = 2
  def mProb2UNSAT(A: Set[Int], B: Set[Int]) : Boolean = {
    !(
      (A -- B).min == (B -- A).min && (A -- B).size == 2
    )
  } holds 

 //A = B1 U B2 U B3 ^ Min(B1) < Max(B2) ^ Min(B2) < Max(B3) ^  |B1| = |B2| ^ |B2| = |B3| ^
  //|A| = 12 ^ Min(A) = 1 ^ Max(A) = 12 ^ |B1|>0 ^ |B2|>0 ^ |B3|>0
  def mTriPart1SAT(A: Set[Int], B1: Set[Int], B2: Set[Int], B3: Set[Int]) : Boolean = {
    !(
      A == (B1 ++ B2 ++ B3) && B1.min < B2.max && B2.min < B3.max && B1.size == B2.size && 
      B2.size == B3.size && A.size == 12 && A.min == 1 && A.max == 12 && B1.size > 0 &&
      B2.size > 0 && B3.size > 0
    )
  } holds 
 
  //|Left|>0 ^ |Right| > 0 ^ !((Max(Left) < value ^ value < Min(Right)  ^ element< value) => 
  //=> (element in (Left U Value U Right) <=> element in Left)) ^ Set(value) = Value
  def mBinFind2UNSAT(value: Int, element: Int,  Left: Set[Int], Right: Set[Int], Valuee: Set[Int]) : Boolean = {
    require(
      Left.size > 0 && Right.size > 0 && Set(value) == Valuee && 
      Left.max < value && 
      value < Right.min && 
      element < value 
    )
      (Left ++ Valuee ++ Right).contains(element) == Left.contains(element) 
  } holds 
  
  // A => B as !A || B  
  //|Left|>0 ^ |Right| > 0 ^ ((Max(Left) < value ^ value < Min(Right)  ^ element< value) =>
  //(element in (Left U Value U Right) <=> element in Left)) ^ Set(value) = Value
  def mNegBinFind2SAT(value: Int, element: Int,  Left: Set[Int], Right: Set[Int], Valuee: Set[Int]) : Boolean = {
    !(
      Left.size > 0 && Right.size > 0 && (!( Left.max < value && value < Right.min && element < value) ||
      ((Left ++ Valuee ++ Right).contains(element) == Left.contains(element) )) && Set(value) == Valuee
    )
  } holds 
   
  //|OldAbove|> 0 ^ |NewAbove| > 0 ^ !((OldAbove = Set() v pivot < Min(OldAbove)  ^ !(e <= pivot) ^
  //NewAbove = OldAbove U Set(e)) => pivot < Min(NewAbove))""", false, "Pivot_3")
  def mPivot3UNSAT(pivot: Int, e: Int,  OldAbove: Set[Int], NewAbove: Set[Int]) : Boolean = {
    require (
      OldAbove.size > 0 && 
      NewAbove.size > 0 && 
      pivot < OldAbove.min &&
      e > pivot &&
      NewAbove == (OldAbove ++ Set(e))
    )
    pivot < NewAbove.min
  } holds 

  
  // A => B as !A || B  
  //|OldAbove|> 0 ^ |NewAbove| > 0 ^ ((OldAbove = Set() v pivot < Min(OldAbove)  ^ !(e <= pivot) 
  //^ NewAbove = OldAbove U Set(e)) => pivot < Min(NewAbove))
  def mNegPivot3SAT(pivot: Int, e: Int,  OldAbove: Set[Int], NewAbove: Set[Int]) : Boolean = {
    !(
      OldAbove.size > 0 && NewAbove.size > 0 && (!( OldAbove == Set.empty[Int] || pivot < OldAbove.min &&
      !( e <= pivot ) && NewAbove == (OldAbove ++ Set(e))) ||
       pivot < NewAbove.min)
    )
  } holds 
   
  //|OldSet| > 0 ^ !((NewSet = OldSet U Set(large) ^ large >= Max(OldSet)) => Max(NewSet) = large)
  def mAddSup4UNSAT(large: Int,  OldSet: Set[Int], NewSet: Set[Int]) : Boolean = {
    //!(
    //  OldSet.size > 0 && !(!(NewSet == (OldSet ++ Set(large)) && large >= OldSet.max) || NewSet.max == large)
    //)
    require(
      OldSet.size > 0 && 
      NewSet == (OldSet ++ Set(large)) && 
      large >= OldSet.max
    )
    NewSet.max == large
  } holds 
  
  // A => B as !A || B 
  //|OldSet| > 0 ^ ((NewSet = OldSet U Set(large) ^ large >= Max(OldSet)) => Max(NewSet) = large)
  def mNegAddSup4SAT(large: Int,  OldSet: Set[Int], NewSet: Set[Int]) : Boolean = {
    !(
      OldSet.size > 0 && (!(NewSet == (OldSet ++ Set(large)) && large >= OldSet.max) || NewSet.max == large)
    )
  } holds 
  
  //|OldSet| > 0 ^ !((NewSet = OldSet U Set(large) ^ large > Max(OldSet)) => Max(NewSet) >= Max(OldSet))
  def mAddSup5UNSAT(large: Int,  OldSet: Set[Int], NewSet: Set[Int]) : Boolean = {
    //!(
    //  OldSet.size > 0 && !(!(NewSet == (OldSet ++ Set(large)) && large >= OldSet.max) || NewSet.max >= OldSet.max)
    //)
    require(
      OldSet.size > 0 && 
      NewSet == (OldSet ++ Set(large)) && 
      large >= OldSet.max 
    )
    NewSet.max >= OldSet.max
  } holds
  
  // A => B as !A || B 
  //|OldSet| > 0 ^ ((NewSet = OldSet U Set(large) ^ large > Max(OldSet)) => Max(NewSet) >= Max(OldSet))
  def mNegAddSup5SAT(large: Int,  OldSet: Set[Int], NewSet: Set[Int]) : Boolean = {
    !(
      OldSet.size > 0 && (!(NewSet == (OldSet ++ Set(large)) && large >= OldSet.max) || NewSet.max >= OldSet.max)
    )
  } holds 
  
  // A => B as !A || B 
  //|OldSet|>0 ^ !((NewSet = Oldset U Set(large) ^ large +1 >= Max(OldSet)) => Max(NewSet) = large)
  def mAddSupLS6SAT(large: Int,  OldSet: Set[Int], NewSet: Set[Int]) : Boolean = {
    !(
      OldSet.size > 0 && !(!(NewSet == (OldSet ++ Set(large)) && large + 1 >= OldSet.max) || NewSet.max == large)
    )
  } holds */
  
/*  //!((Set = Elem U Rest ^ elem >= Max(Rest)) => Max(Set) = elem) ^ Elem = Set(elem)
  def mUneqPart7UNSAT(elem: Int,  mySet: Set[Int], ElemSet: Set[Int], Rest: Set[Int]) : Boolean = {
    require(
      mySet == ElemSet ++ Rest &&
      elem >= Rest.max && 
      ElemSet == Set(elem) 
    )
    mySet.max == elem
  } holds
  
  //((Set = Elem U Rest ^ elem >= Max(Rest)) => Max(Set) = elem) ^ Elem = Set(elem)
  def mNegUneqPart7SAT(elem: Int,  mySet: Set[Int], ElemSet: Set[Int], Rest: Set[Int]) : Boolean = {
    !(
      ! ( mySet == ElemSet ++ Rest &&
      elem >= Rest.max && 
      ElemSet == Set(elem) ) ||   mySet.max == elem
    )
  } holds 
  
  //!( (Max(LeftTree) < value1 ^ value1 < Min(MiddleTree) ^ Max(LeftTree U Value1 U MiddleTree) < Min(Value2) ^ 
  //value1 < value2 ^ value2 < Min(RightTree) ^ |LeftTree|>0 ^ |MiddleTree| > 0 ^ |RightTree| > 0^ 
  //Value1 = Set(value1) ^ Value2 = Set(value2)) => 
  //(Min(LeftTree) < value1 ^ Min(Value1) < Max(MiddleTree U Value2 U RightTree) ^ 
  //Max(MiddleTree) < value2 ^ value2 < Min(RightTree)))
  def mZigZig8UNSAT(value1: Int, value2: Int, Value1: Set[Int], Value2: Set[Int], LeftTree: Set[Int], MiddleTree: Set[Int], RightTree: Set[Int]) : Boolean = {
    require(
      LeftTree.max < value1 && value1 < MiddleTree.min && (LeftTree ++ Value1 ++ MiddleTree).max < Value2.min &&
      value1 < value2 && value2 < RightTree.min && LeftTree.size >0 && MiddleTree.size > 0 && RightTree.size > 0 &&
      Value1 == Set(value1) && Value2 == Set(value2) 
    )
      LeftTree.min < value1 && Value1.min < (MiddleTree ++ Value2 ++ RightTree).max && 
      MiddleTree.max < value2 && value2 < RightTree.min 
  } holds*/ 
  
  def mNegZigZig8SAT(value1: Int, value2: Int, Value1: Set[Int], Value2: Set[Int], LeftTree: Set[Int], MiddleTree: Set[Int], RightTree: Set[Int]) : Boolean = {
    !(!(
      LeftTree.max < value1  && value1 < MiddleTree.min && (LeftTree ++ Value1 ++ MiddleTree).max < Value2.min &&
      value1 < value2 && value2 < RightTree.min && LeftTree.size >0 && MiddleTree.size > 0 && RightTree.size > 0 &&
      Value1 == Set(value1) && Value2 == Set(value2) 
      ) ||
      (LeftTree.min < value1 && Value1.min < (MiddleTree ++ Value2 ++ RightTree).max
      && MiddleTree.max < value2 && value2 < RightTree.min)
    )
  } holds 
  
  //((Max(LeftTree) < value1 ^ value1 < Min(MiddleTree) ^ Max(LeftTree U Value1 U MiddleTree) < Min(Value2) ^ 
  //value1 < value2 ^ value2 < Min(RightTree) ^ |LeftTree|>0 ^ |MiddleTree| > 0 ^ |RightTree| > 0^ 
  //Value1 = Set(value1) ^ Value2 = Set(value2)) => 
  //(Min(LeftTree) < value1 ^ Min(Value1) < Max(MiddleTree U Value2 U RightTree) ^ 
  //Max(MiddleTree) < value2 ^ value2 < Min(RightTree)))
/*  def mNegZigZig8SAT(value1: Int, value2: Int, Value1: Set[Int], Value2: Set[Int], LeftTree: Set[Int], MiddleTree: Set[Int], RightTree: Set[Int]) : Boolean = {
    !(!(
      LeftTree.max < value1 && value1 < MiddleTree.min && (LeftTree ++ Value1 ++ MiddleTree).max < Value2.min &&
      value1 < value2 && value2 < RightTree.min && LeftTree.size >0 && MiddleTree.size > 0 && RightTree.size > 0 &&
      Value1 == Set(value1) && Value2 == Set(value2) 
      ) ||
      (LeftTree.min < value1 && Value1.min < (MiddleTree ++ Value2 ++ RightTree).max && 
      MiddleTree.max < value2 && value2 < RightTree.min)
    )
  } holds */
    
/*  //!((A U B = C ^ Max(A) < Min(B)) <=> (A subseteq C ^ B = C \ A ^ Max(A) < Min(B)))
  def mEqPart9UNSAT(elem: Int,  A: Set[Int], B: Set[Int], C: Set[Int]) : Boolean = {
    (A ++ B == C && A.max < B.min) == (A.subsetOf(C) && B == C -- A && A.max < B.min)
  } holds
  
  //((A U B = C ^ Max(A) < Min(B)) <=> (A subseteq C ^ B = C \ A ^ Max(A) < Min(B)))
  def mNegEqPart9SAT(elem: Int,  A: Set[Int], B: Set[Int], C: Set[Int]) : Boolean = {
    !(A ++ B == C && A.max < B.min) == (A.subsetOf(C) && B == C -- A && A.max < B.min)
  } holds
  
  def mAddSup5mmUNSAT(large: Int,  OldSet: Set[Int], NewSet: Set[Int]) : Boolean = {
    !(
      OldSet.size > 0 && NewSet == OldSet ++ Set(large) && NewSet.max < OldSet.max
    )
  } holds
  
  def newProblemUNSAT(x: Int, y: Int, A: Set[Int], B: Set[Int]) : Boolean = {
    require (
      A.contains(x) && 
      B.contains(y) && 
      A.max < B.min
    )
      x < y
  } holds 
  
  def newVC1SAT(x: Int, size: Int, Content: Set[Int]): Boolean = { 
    require (
      ! Content.contains(x) &&
      size == Content.size
    )
      (size == 0) == (Content == Set.empty[Int])
  } holds
  
  def newVC2SAT(x: Int, size: Int, Content: Set[Int]): Boolean = { 
    require (
      ! Content.contains(x) &&
      size == Content.size
    )
      size + 1 == (Set(x) ++ Content).size
  } holds
  
  def newVC3SAT(x: Int, size: Int, size1: Int,  Content: Set[Int]): Boolean = { 
    require (
      size == Content.size &&
      size1 == (Set(x) ++ Content).size
    )
      size1 <= size + 1
  } holds
  
  def newVC4SAT(x1: Int, x2: Int, x3: Int, Content: Set[Int], Alloc: Set[Int]): Boolean = { 
    require (
      Content.subsetOf(Alloc) &&
      ! Alloc.contains(x1) && 
      ! (Alloc ++ Set(x1) ).contains(x2) && 
      ! (Alloc ++ Set(x1) ++ Set(x2) ).contains(x3)
    )
      (Content ++ Set(x1) ++ Set(x2) ++ Set(x3) ).size == Content.size + 3
  } holds
  
  def newVC5SAT(x1: Int, x2: Int, x3: Int, Content: Set[Int], Alloc0: Set[Int], Alloc1: Set[Int], Alloc2: Set[Int]): Boolean = { 
    require (
      Content.subsetOf(Alloc0) &&
      ! Alloc0.contains(x1) &&
      (Alloc0 ++ Set(x1)).subsetOf(Alloc1) &&
      ! Alloc1.contains(x2) &&
      (Alloc1 ++ Set(x2) ).subsetOf(Alloc2) &&
      ! Alloc2.contains(x3)
    )
      (Content ++ Set(x1) ++ Set(x2) ++ Set(x3) ).size == Content.size + 3
  } holds
  
  def newVC6SAT(x: Int, C: Set[Int], C1: Set[Int], Alloc0: Set[Int], Alloc1: Set[Int], Alloc2: Set[Int]): Boolean = { 
    require (
      C.contains(x) && 
      C1 == C -- Set(x) &&
      (Alloc1 -- Alloc0).size <= 1 &&
      (Alloc2 -- Alloc1).size <= C1.size
    )
      (Alloc2 -- Alloc0).size <= C.size
  } holds */
  
}