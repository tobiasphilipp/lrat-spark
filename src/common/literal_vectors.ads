pragma Unevaluated_Use_Of_Old (Allow);

with Vector;		
with SAT;		
          
package Literal_Vectors		
is new	
    Vector
      (Element_Type => SAT.Literal_Type, Magic_Element => 1);
