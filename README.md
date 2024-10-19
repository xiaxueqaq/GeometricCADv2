# GeometricCADv2
A new cylindrical algebraic decomposition algorithm that makes use of all equations, based on algebraic geometry.

# Dependency
- Mathematica 13

# Install
1. Download `GeometricCADv2.wl`.
2. You can open it and run all codes so you can use the functions in it.

# Usage
`GeometricCAD[L,x]` accepts a list of (generators of) ideals $L$ and a list of variables $x$ as input, the result is a c.a.d. adapted to the varieties defined by the ideals. The output is in the sample point representation, though an extended-Tarski description is possible with several modifications.

# Example

In[1] = `GeometricCAD[{{x^3 + p x + q, 4 p^3 + 27 q^2}}, {p, q, x}]`

Out[1] = `{{{-1}, {0}, {1}}, {{-1, -(2/(3 Sqrt[3]))}, {-1, 2/(3 Sqrt[3])}, {0, 
   0}}, {{-1, -(2/(3 Sqrt[3])), 
   Root[{-4 + 27 #^2& , # - #2 + #2^3& }, {1, 1}]}, {-1, -(2/(
    3 Sqrt[3])), Root[{-4 + 27 #^2& , # - #2 + #2^3& }, {1, 3}]}, {-1,
    2/(3 Sqrt[3]), 
   Root[{-4 + 27 #^2& , # - #2 + #2^3& }, {2, 1}]}, {-1, 2/(
   3 Sqrt[3]), Root[{-4 + 27 #^2& , # - #2 + #2^3& }, {2, 2}]}, {0, 0,
    0}}}`
