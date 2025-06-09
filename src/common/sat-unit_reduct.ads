--------------------------------------------------------------------------------
--                                                                            --
-- Verified Datastructures and Algorithms for Satisfiability Testing          --
--                                                                            --
--------------------------------------------------------------------------------
--                                                                            --
-- This file contains the unit under a reduct specification and corresponding --
-- lemmas.                                                                    --
--                                                                            --
--------------------------------------------------------------------------------
--                                                                            --
-- Copyright (C) 2021-2023, Tobias Philipp                                    --
--                                                                            --
--------------------------------------------------------------------------------

package SAT.Unit_Reduct 
with SPARK_Mode => On,
  Always_Terminates
is
   -- A1 /\ F1   entails A2 /\ F2
   
   function Consequence
     (F1 : Formula_Type;
      A1 : Assignment_Type;
      F2 : Formula_Type;
      A2 : Assignment_Type)
      return Boolean
   is (for all I of Interpretations =>
         (if Satisfies (I, F1) and Satisfies (I, A1) 
          then Satisfies (I, F2) and Satisfies (I, A2)))
     with Ghost;
   
   
   -- A1 /\ F1   EQUIV  A2 /\ F2
   function Equivalent
     (F1 : Formula_Type;
      A1 : Assignment_Type;
      F2 : Formula_Type;
      A2 : Assignment_Type)
      return Boolean
   is (Consequence (F1, A1, F2, A2) and Consequence(F2, A2, F1, A1))
     with Ghost;
   

   -- A clause is unit clause of the form [L] under A (reduct)
   function Spec
     (C : Clause_Type;
      A : Assignment_Type;
      L : Literal_Type) return Boolean
   is ( -- the clause is not satisfied under A
        (for all Lp of C => not Is_True (A, Lp)) and then
        -- all literals except L are false under A
          (for all Lp of C => (if Lp /= L then Is_False (A, Lp))) and then
        -- L appears in C
        Appears (C, L)
       );
   
   -- Usually, when found a unit clause in the reduct, we would like to
   -- "propagate" the unit literal; and therefore extend the assignment
   function Propagate
     (A  : Assignment_Type;
      Ap : Assignment_Type;
      F  : Formula_Type) return Boolean
   is (for some C of F =>
         (for some L of C =>
            (Spec (C, A, L) and then
             Ap = Assignment_Vector.Add (A, L))))
     with Pre => Assignment_Vector.Last (A) < Positive'Last, Ghost;
   
   -- This lemma states that 
   procedure Propagate_Lemma
     (A  : in Assignment_Type;
      Ap : in Assignment_Type;
      F  : in Formula_Type)
     with
       Pre  => Assignment_Vector.Last (A) < Positive'Last and then Propagate (A, Ap, F),
     Post => Equivalent (F, A, F, Ap),
     Ghost;
   
   function Assignment_Clause (A : Assignment_Type; C : Clause_Type) return Boolean
   is ((for all L of C => Appears (A, -L)) and (for all L of A => Appears (C, -L)))
       with Ghost;
   
   procedure Propagate_RUP_Lemma
     (A  : in Assignment_Type;
      Ap : in Assignment_Type;
      C  : in Clause_Type;
      F  : in Formula_Type)
     with Pre =>
       Equivalent (F, A, F, Ap) and then 
       (for some C of F => (for all L of C => Is_False (Ap, L))) and then
       Assignment_Clause (A, C) and then
       Clause_Vector.Last (F) < Positive'Last,
       Post => Consequence (F, F.Add (C)),
         Ghost;
     

end SAT.Unit_Reduct;
