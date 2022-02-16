#define F() 1

int foo(int);

int bar(int x)
{
    if (x)
    {
        return foo(x - 1);
    }
    return 0;
}

int foo(int x)
{
    return bar(x);
}

int main(int argc, char const *argv[])
{
    foo(1);
    F();
    return 0;
}
