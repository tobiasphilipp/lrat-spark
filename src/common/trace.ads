--------------------------------------------------------------------------------
--                                                                            --
-- A verified proof checker written in SPARK 2014                             --
--                                                                            --
-- This file contains procedures for tracing debug information.               --
--                                                                            --
--------------------------------------------------------------------------------
--                                                                            --
-- Copyright (C) 2021-2023, Tobias Philipp                                    --
--                                                                            --
--------------------------------------------------------------------------------

with GNAT.Source_Info;
with SPARK.Big_Integers;

package Trace 
  with SPARK_Mode
is
   use type SPARK.Big_Integers.Big_Integer;
   
   type Level_Type is 
     (Trace, -- Anything useful for tracing the execution
      Debug, -- Anything useful 
      Info,  -- Few messages about what the system does
      Warn,  -- 
      Error, -- Invalid input, RUP or RAT check failed etc
      Fatal  -- A crash of the system that cannot be handled (out of memory)
     );
   
   Configured_Level : constant Level_Type := Trace;
   
   procedure Put_Line
     (Level       : in Level_Type;
      Line        : in String;
      Indentation : in Natural    := 0;
      Enclosing   : in String     := GNAT.Source_Info.Enclosing_Entity;
      Src_Info    : in String     := GNAT.Source_Info.Source_Location)
     with 
       Pre => SPARK.Big_Integers.To_Big_Integer (Line'Length) +
         SPARK.Big_Integers.To_Big_Integer (Indentation) +
         SPARK.Big_Integers.To_Big_Integer (Enclosing'Length) +
           SPARK.Big_Integers.To_Big_Integer (Src_Info'Length) 
             <= SPARK.Big_Integers.To_Big_Integer (2**30),
     Inline;

end Trace;
