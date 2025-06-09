--------------------------------------------------------------------------------
--                                                                            --
-- Verified Datastructures and Algorithms for Satisfiability Testing          --
--                                                                            --
--------------------------------------------------------------------------------
--                                                                            --
-- This file contains the unit specification and a simple lemma.              --
--                                                                            --
--------------------------------------------------------------------------------
--                                                                            --
-- Copyright (C) 2021-2023, Tobias Philipp                                    --
--                                                                            --
--------------------------------------------------------------------------------

package SAT.Unit
with SPARK_Mode => On,
  Always_Terminates
is

   function Is_Unit (C : Clause_Type)
                     return Boolean
   is (C'Length = 1);
   
   procedure Lemma
     (F : Formula_Type;
      C : Clause_Type)
     with Pre => Contains (F, C) and then Is_Unit (C),
     Post => (for all I of Interpretations => (if Satisfies (I, F) then Satisfies (I, C (0)))),
       Global => null;
   

end SAT.Unit;
