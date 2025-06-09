pragma Unevaluated_Use_Of_Old (Allow);

with Vector;	

package Integer_Vectors is new	
  Vector
    (Element_Type => Integer, Magic_Element => 0);
      --(Element_Type => Sid.Clause_Storage.Clause_Ref, Magic_Element => 1);
