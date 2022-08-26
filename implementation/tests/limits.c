#include <stdio.h>
#include <limits.h>

#define MAX_U16 (USHRT_MAX)
#define MAX_I16 (SHRT_MAX)
#define MAX_U32 (UINT_MAX)
#define MAX_I32 (INT_MAX)

int main(int argc, char **argv) {
    printf("%u\n",
        // Should transform
        MAX_U16
    );
    printf("%u\n",
        // Should transform
        (MAX_U16)
        +
        // Should transform
        (MAX_U16)
    );
    printf("%u\n",
        // Should transform
        (MAX_U16)
        -
        // Should transform
        (MAX_U16)
    );
    printf("%u\n",
        // Should transform
        (MAX_U16)
        *
        // Should transform
        (MAX_U16)
    );
    printf("%u\n",
        // Should transform
        (MAX_U16)
        /
        // Should transform
        (MAX_U16)
    );

    printf("%u\n",
        // Should transform
        MAX_I16
    );
    printf("%u\n",
        // Should transform
        (MAX_I16)
        +
        // Should transform
        (MAX_I16)
    );
    printf("%u\n",
        // Should transform
        (MAX_I16)
        -
        // Should transform
        (MAX_I16)
    );
    printf("%u\n",
        // Should transform
        (MAX_I16)
        *
        // Should transform
        (MAX_I16)
    );
    printf("%u\n",
        // Should transform
        (MAX_I16)
        /
        // Should transform
        (MAX_I16)
    );


    printf("%u\n",
        // Should transform
        MAX_U32
    );
    printf("%u\n",
        // Should transform
        (MAX_U32)
        +
        // Should transform
        (MAX_U32)
    );
    printf("%u\n",
        // Should transform
        (MAX_U32)
        -
        // Should transform
        (MAX_U32)
    );
    printf("%u\n",
        // Should transform
        (MAX_U32)
        *
        // Should transform
        (MAX_U32)
    );
    printf("%u\n",
        // Should transform
        (MAX_U32)
        /
        // Should transform
        (MAX_U32)
    );

    printf("%u\n",
        // Should transform
        MAX_I32
    );
    printf("%u\n",
        // Should transform
        (MAX_I32)
        +
        // Should transform
        (MAX_I32)
    );
    printf("%u\n",
        // Should transform
        (MAX_I32)
        -
        // Should transform
        (MAX_I32)
    );
    printf("%u\n",
        // Should transform
        (MAX_I32)
        *
        // Should transform
        (MAX_I32)
    );
    printf("%u\n",
        // Should transform
        (MAX_I32)
        /
        // Should transform
        (MAX_I32)
    );

    return 0;
}