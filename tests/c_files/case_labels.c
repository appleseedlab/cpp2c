#define RED 1
#define GREEN 2
#define BLUE 3
#define MAGENTA 4
#define CYAN 5
#define YELLOW 6

int main(void)
{

    int color = 0;

    switch (color)
    {
    case RED:
    case GREEN:
        switch (color)
        {
        case RED:
        case MAGENTA:
            break;

        default:
            break;
        }
        break;
    case BLUE:
        switch (color)
        {
        case MAGENTA:
            switch (color)
            {
            case YELLOW:
                break;
            case CYAN:
                break;
            default:
                break;
            }
            break;

        default:
            break;
        }
        break;
    default:
        break;
    }

    return 0;
}