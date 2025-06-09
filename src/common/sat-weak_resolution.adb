pragma Unevaluated_Use_Of_Old (Allow);

with Ada.Text_IO;

--with Vector;		

with SPARK.Cut_Operations;
use SPARK.Cut_Operations;





package body SAT.Weak_Resolution
with SPARK_Mode
is

   -- --------------------------------------------------------------------------

   -- We use the following Copy operation to copy parts of clause into the
   -- resolvent.
   procedure Copy
     (Data   : in     Clause_Type;
      From   : in     Natural;
      Length : in     Natural;
      Dest   : in out Clause_Type;
      Index  : in     Natural)
     with
     Pre  =>
     (Length = 0 or  --  If the length is zero, nothing is done and therefore
	             --  all other conditions can be arbitrary
	(Dest'First <= Index and then
	 Index + Length - 1 <= Dest'Last and then
	 Data'First <= From and then
	 From + Length - 1 <= Data'Last)),
     Post =>
     -- We copied parts of the clause
     (for all I in 0 .. Length - 1 => Dest (Index + I) = Data (From + I)) and
     -- And the rest remains unchanged:
       (for all I in Dest'Range =>
	  (if I < Index or I > Index + Length then Dest (I) = Dest'Old (I)))
   is
   begin
      for L in 0 .. Length - 1
      loop
	 Dest (Index + L) := Data (From + L);

	 -- Copy
	 pragma Loop_Invariant
	   (for all J in 0 .. L =>
	      Dest (Index + J) = Data (From + J));

	 -- No change
	 pragma Loop_Invariant
	   (for all I in Dest'Range =>
	      (if I < Index or I > Index + Length
		 then Dest (I) = Dest'Loop_Entry (I)));
      end loop;

   end Copy;

   -- --------------------------------------------------------------------------

   -- Gets the position of a literal L in a clause C
   function Get_Literal_Pos
     (C : Clause_Type;
      L : Literal_Type)
     return Natural
   with
     Pre => Appears (C, L),
     Post => (Get_Literal_Pos'Result in C'Range and
	      C (Get_Literal_Pos'Result) = L)
   is
   begin
      for I in C'Range
      loop
	 if
	   C (I) = L
	 then
	    return I;
	 end if;

	 -- Literal not found
	 pragma Loop_Invariant
	   (for all J in C'First .. I =>
	      C (J) /= L);
      end loop;

      return C'First;
   end Get_Literal_Pos;

   -- --------------------------------------------------------------------------
   
   

          
   --  package Literal_Vectors
   --  is new
   --    Vector
   --      (Element_Type => Literal_Type, Magic_Element => 1);
   --  
   --  V : Literal_Vectors.Vector;

   function Resolve
     (C : Clause_Type;
      D : Clause_Type;
      L : Literal_Type)
      return Clause_Type
   is
      C_No_Duplicates : Clause_Type := Remove_Duplicate_Literals (C);
      Result : Clause_Type (0 .. C_No_Duplicates'Length + D'Length - 1) := (others => 1);
      P : Natural := C_No_Duplicates'Last + 1;
   begin
      Result (0 .. C_No_Duplicates'Last) := C_No_Duplicates;
      
      
      for I in D'Range
      loop
         pragma Loop_Invariant (P > C_No_Duplicates'Last);
         pragma Loop_Invariant (P <= C_No_Duplicates'Last + I + 1);
         pragma Loop_Invariant (for all Lit of C => Appears (Result (0 .. C_No_Duplicates'Last), Lit));
         pragma Loop_Invariant (for all Lit of D (0 .. I - 1) => (if Lit /= -L then Appears (Result (0 .. P - 1), Lit)));
         pragma Loop_Invariant (for all Lit of Result (0 .. P - 1) => (if Lit = -L then Appears (C, Lit) else (Appears (C, Lit) or else Appears (D, Lit))));
         pragma Loop_Invariant (Has_No_Duplicates (Result (0 .. P - 1)));
         
         if D (I) /= -L and then not Appears (Result (0 .. P - 1), D (I)) -- more expensive than necessary
         -- if D (I) /= -L and then not Appears (C, D (I)) -- cheap
         then
            Result (P) := D (I);
            P := P + 1;
         end if;
      end loop;
      
      return Result (0 .. P - 1);
   end Resolve;
   
   procedure Workaround_Resolve_Equality
     (C, D, E : Clause_Type;
      Pivot : Literal_Type)
   is
   begin
      pragma Assert (for all L of Weak_Resolution.Resolve (C, D, Pivot) =>
                       Appears (Weak_Resolution.Resolve (C, E, Pivot), L));
      pragma Assert (for all L of Weak_Resolution.Resolve (C, E, Pivot) =>
                       Appears (Weak_Resolution.Resolve (C, D, Pivot), L));
   end Workaround_Resolve_Equality;

   
   procedure Lemma_Interpretation
     (F : in Formula_Type;
      C : in Clause_Type;
      D : in Clause_Type;
      L : in Literal_Type;
      R : in Clause_Type;
      I : in Interpretation_Type)
   is
   begin
      null;
   end Lemma_Interpretation;
   
     procedure Lemma
     (F : in Formula_Type;
      C : in Clause_Type;
      D : in Clause_Type;
      L : in Literal_Type;
      R : in Clause_Type)
   is
   begin
      null;
   end Lemma;
   
   --Successful_Initialization : Boolean;
-- begin
   
   --V.Init (Successful_Initialization);

end SAT.Weak_Resolution;
