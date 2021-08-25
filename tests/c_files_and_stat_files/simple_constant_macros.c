// Macro    |   Expected Type
#define A 1               // int
#define B +1              // int
#define C -1              // int
#define D 1.0             // double
#define E +1.0            // double
#define F -1.0            // double
#define G 'G'             // char
#define H "Hello, World!" // string
#define I '\n'            // char
#define J "This" \
          "is"   \
          "a"    \
          "joke"

/*
TODO: Add more types, and handle negative values
https://www.tutorialspoint.com/cprogramming/c_data_types.htm
Integer Types
char	        1 byte	                            -128 to 127 or 0 to 255
unsigned char	1 byte	                            0 to 255
signed char	    1 byte	                            -128 to 127
int	            2 or 4 bytes	                    -32,768 to 32,767 or -2,147,483,648 to 2,147,483,647
unsigned int	2 or 4 bytes	                    0 to 65,535 or 0 to 4,294,967,295
short	        2 bytes	                            -32,768 to 32,767
unsigned short	2 bytes	                            0 to 65,535
long	        8 bytes or (4bytes for 32 bit OS)	-9223372036854775808 to 9223372036854775807
unsigned long	8 bytes	                            0 to 18446744073709551615
Floating-Point Types
float	        4 byte      1.2E-38 to 3.4E+38	    6 decimal places
double	        8 byte      2.3E-308 to 1.7E+308	15 decimal places
long double	    10 byte     3.4E-4932 to 1.1E+4932	19 decimal places
*/

/*
Storage size for float : 4 
FLT_MAX      :   3.40282e+38
FLT_MIN      :   1.17549e-38
-FLT_MAX     :   -3.40282e+38
-FLT_MIN     :   -1.17549e-38
DBL_MAX      :   1.79769e+308
DBL_MIN      :   2.22507e-308
-DBL_MAX     :  -1.79769e+308
Precision value: 6
*/