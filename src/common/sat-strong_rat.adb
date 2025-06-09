package body SAT.Strong_RAT is

   procedure Satisfies_Consequence
     (F : Formula_Type;
      C : Clause_Type;
      I : Interpretation_Type)
   is
   begin
      Completeness (I);
      null;
   end;
   
   procedure Equivalence_Consequence 
     (F : Formula_Type;
      C, D : Clause_Type)
   is
   begin
      null;
   end Equivalence_Consequence;
   
   procedure Resolution_Appears
     (C, D : Clause_Type;
      L : Literal_Type)
   is
   begin
      null;
   end Resolution_Appears;

   procedure Lemma_Interpretation
     (F : Formula_Type;
      C : Clause_Type;
      L : Literal_Type;
      I : Interpretation_Type)
   is
   begin
      if Satisfies (Guard (I, L), F) or Satisfies (Guard (I, -L), C) then
         return;
      end if;
      
      pragma Assert (for all D of F =>
                       (if Appears (D, -L) then
                             Consequence (F, Weak_Resolution.Resolve (C, D, L))));
      pragma Assert
        (Satisfies (Guard (I, -L), F) and then 
           (for all D of F =>
                (if Appears (D, -L) then
                        Consequence (F, Weak_Resolution.Resolve (C, D, L)) and then 
                        Satisfies (Guard (I, -L), Weak_Resolution.Resolve (C, D, L))
                )));
            
      pragma Assert (Satisfies (Guard (I, L), C));
      if Satisfies (Guard (I, L), F) then
         return;
      end if;

      pragma Assert (for some D of F => (not Satisfies (Guard (I, L), D)));
      pragma Assert (not Appears (C, -L));
      pragma Assert (for all Lp of C => not Appears (C, -Lp));
               
      pragma Assert (for some D of F => not Satisfies (Guard (I, L), D));
                              
      pragma Assert 
        (for all D of F => 
           (if not Satisfies (Guard (I, L), D) then
                (
                 (for all Lp of D => not Satisfies (Guard (I, L), Lp)) and then
                   (for all L of D => not Appears (D, -L)) and then
                 Appears (D, -L) and then
                       not Appears (D, L) and then
                       not Appears (C, -L) and then 
                     -- I [-L] |= F, I[-L] not |= C
                 Satisfies (Guard (I, -L), Weak_Resolution.Resolve (C, D, L)) and then
                   (for some Lp of Weak_Resolution.Resolve (C, D, L) =>
                        Satisfies (I, Lp)) and then
                     (for all Lp of Weak_Resolution.Resolve (C, D, L) => Lp /= -L) and then
                   (for some Lp of Weak_Resolution.Resolve (C, D, L) =>
                        Satisfies (I, Lp) and then (Appears (C, Lp) or else Appears (D, Lp))) and then
                     (for some Lp of Weak_Resolution.Resolve (C, D, L) =>
                            Satisfies (I, Lp) and then (Appears (C, Lp) or else Appears (D, Lp)) and then Lp /= L and then Lp /= -L)
                )
           ));
      pragma Assert (False);
   end Lemma_Interpretation;
      
   procedure Lemma
     (F : Formula_Type;
      C : Clause_Type;
      L : Literal_Type)
   is
   begin
      if Satisfiable (F) then
         pragma Assert (for some J of Interpretations => Satisfies (J, F));
         pragma Assert (for some I of Interpretations => Satisfies (I, F) and then
                        (
                         (Satisfies (Guard (I, L), F) and then Satisfies (Guard (I, L), C)) or else
                               (Satisfies (Guard (I, -L), F) and then Satisfies (Guard (I, -L), C))
                          ) and then
                        (
                         Satisfies (Guard (I, L), F.Add (C)) or else
                             Satisfies (Guard (I, -L), F.Add (C))
                            ));
                        
         pragma Assert (Satisfiable (F.Add (C)));
         null;
      else
         pragma Assert (not Satisfiable (F.Add (C)));
         null;
      end if;
   end Lemma;


end SAT.Strong_RAT;
