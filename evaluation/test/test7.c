struct x {
    struct {
        int z;
    } y;
};

#define GET_Y_Z(b) b.z

int main(int argc, char **argv) {
    struct x a;
    // 1 unique invocation
    // should not transform
    GET_Y_Z(a.y);
    return 0;
}