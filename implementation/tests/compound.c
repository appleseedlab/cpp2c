#include <stdio.h>

#define ONE 1

int main()
{
    {
        // Should transform
        printf(
            "%d\n",
            ONE
        );

        {
            // Should transform
            printf(
                "%d\n",
                ONE
            );

            {
                // Should transform
                printf(
                    "%d\n",
                    ONE
                );

                {}

                {
                }

                // Should transform
                printf(
                    "%d\n",
                    ONE
                );
            }
        }
    }
    return 0;
}
