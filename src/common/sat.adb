package body SAT
with SPARK_Mode => On
is   
	
   function Interpretations return All_Interpretations 
   is	    
    X : All_Interpretations; 
   begin    		     
    return X;
   end Interpretations;	


   function Next_Interpretation (K : All_Interpretations; I : Interpretation_Cursor_Type) return Interpretation_Cursor_Type
   is
      Result : Interpretation_Type := I.I;
      Previous : Boolean;
   begin
      if I.Overflow
      then
         return Interpretation_Cursor_Type'(Overflow => True, I => (others => False));
      end if;
      
      if (for all L of I.I => L = True)
      then
         return Interpretation_Cursor_Type'(Overflow => True, I => (others => False));
      end if;
      
      for J in I.I'Range
      loop
         Previous := Result (J);
         Result (J) := not Previous;
         if not Previous
         then
            return (Interpretation_Cursor_Type'(Overflow => False, I => Result));
         end if;
      end loop;

      return Interpretation_Cursor_Type'(Overflow => False, I => Result);

   end Next_Interpretation;
   
   
      -- --------------------------------------------------------------------------

   function Remove_Duplicate_Literals
     (C : in Clause_Type) return Clause_Type
   is
      D : Clause_Type (C'First .. C'Last) := C;
      J : Natural := D'First;
   begin

      for I in C'First .. C'Last
      loop
	 pragma Loop_Invariant
	   (J <= I);

	 -- No duplicates so far
	 pragma Loop_Invariant
	   (for all K in D'First .. J - 1 =>
	      (for all Kp in D'First .. J - 1 =>
		 (if K /= Kp then D (K) /= D (Kp))));

	 -- we preserve set equality
	 pragma Loop_Invariant
	   (Subset (D (D'First .. J - 1), C));
	 pragma Loop_Invariant
	   (Subset (C (C'First .. I - 1), D (D'First .. J - 1)));

	 if
	   (for all K in D'First .. J - 1 => D (K) /= C (I))
	 then
	    D (J) := C (I);
	    J := J + 1;
	 end if;
      end loop;

      return D (D'First .. J - 1);
   end Remove_Duplicate_Literals;
   
   procedure Satisfies_Clause_Ordering_Irrelevant
     (I : Interpretation_Type;
      C : Clause_Type;
      D : Clause_Type)
   is
   begin
      null;
   end Satisfies_Clause_Ordering_Irrelevant;
   
   procedure Satisfies_Formula_Ordering_Irrelevant
     (I : Interpretation_Type;
      F : Formula_Type;
      G : Formula_Type)
   is
   begin
      null;
   end Satisfies_Formula_Ordering_Irrelevant;
   
   procedure Satisfiable_Subset
     (F, G : Formula_Type)
   is
   begin
      null;
   end Satisfiable_Subset;


   procedure Empty_Clause_Lemma
     (F : Formula_Type)
   is
   begin
      null;
   end Empty_Clause_Lemma;
   
       procedure Clause_Satisfaction_Ternary
     (I : Interpretation_Type;
      A, B, C : Literal_Type)
   is
   begin
      null;
   end Clause_Satisfaction_Ternary;
   
   procedure Clause_Satisfaction_Binary
     (I : Interpretation_Type;
      A, B : Literal_Type)
   is
   begin
      null;
   end Clause_Satisfaction_Binary;
   
   
      procedure Satisfaction_Implies_Satisfiability
     (F : Formula_Type;
      I : Interpretation_Type)
   is
      X : Interpretation_Cursor_Type := (Overflow => False, I => I);
   begin
      pragma Assert (Interpretation_Element (Interpretations, X) = I);
   end;
       
   
      
   procedure Completeness
     (I : Interpretation_Type)
   is
      X : Interpretation_Cursor_Type := (Overflow => False, I => I);
   begin
      pragma Assert (Interpretation_Element (Interpretations, X) = I);
      null;
   end Completeness;

   
   procedure Equivalence_Implies_Equisatisfiability
     (F, G : Formula_Type)
   is
   begin
      null;
   end Equivalence_Implies_Equisatisfiability;
   
end SAT;
