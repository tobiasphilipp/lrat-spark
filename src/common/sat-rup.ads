--------------------------------------------------------------------------------
--                                                                            --
-- Verified Datastructures and Algorithms for Satisfiability Testing          --
--                                                                            --
--------------------------------------------------------------------------------
--                                                                            --
-- This file contains the RUP definition and core lemma.                      --
--                                                                            --
--------------------------------------------------------------------------------
--                                                                            --
-- Copyright (C) 2021-2023, Tobias Philipp                                    --
--                                                                            --
--------------------------------------------------------------------------------

with SAT.Unit_Reduct;

package SAT.RUP
with SPARK_Mode => On,
  Always_Terminates
is
   function Is_Empty_Clause
     (C : Clause_Type;
      A : Assignment_Type) return Boolean
   is (for all Lp of C => Is_False (A, Lp));

   function Has_Empty_Clause
     (F : Formula_Type;
      A : Assignment_Type) return Boolean
   is (for some C of F => Is_Empty_Clause (C, A));
   
   -- We can represent an assignment A as a clause containing its complementary
   -- literals. Here we generalize it that the clause may contain further literals.
   -- This is OK since if C represent A and C is RUP, then any clause containing D
   -- is RUP as well.
   function Assignment_Clause_Rel
     (A : Assignment_Type;
      C : Clause_Type)
     return Boolean
   is (for all L of A => Appears (C, Compl (L)));

   procedure Lemma
     (A  : in Assignment_Type;
      Ap : in Assignment_Type;
      F  : in Formula_Type;
      C  : in Clause_Type)
   with
     Pre  => Has_Empty_Clause (F, Ap) and
             Unit_Reduct.Equivalent (F, A, F, Ap) and
       Assignment_Clause_Rel (A, C) and
       Clause_Vector.Last (F) < Positive'Last,
     Post => Equisatisfiable (F, Clause_Vector.Add (F, C)),
     Ghost;

end SAT.RUP;
