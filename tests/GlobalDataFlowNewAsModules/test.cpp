char * source1();

void source2(char*, int);

void sink(char*);

void sanitize(char*);
char * append(char *, char*);
int valid(char*);

void unsafe_use(char* ptr) {
    sink(ptr);
}

void sanitized_use(char* ptr) {
    sanitize(ptr);
    sink(ptr);
}

void validated_use(char* ptr) {
    if(valid(ptr)) {
        sink(ptr);
    }
}

void incorrect_validated_use(char* ptr) {
    if(!valid(ptr)) {
        sink(ptr);
    }
}

void missing_edge(char * ptr) {
    char* ptr2 = append(ptr, "world");

    sink(ptr2);
}

int main(int argc, char** argv) {
    char * ptr1 = source1();

    unsafe_use(ptr1);
    sanitized_use(ptr1);
    validated_use(ptr1);
    incorrect_validated_use(ptr1);
    missing_edge(ptr1);

    char * ptr2; 
    source2(ptr2, 10);

    unsafe_use(ptr2);
    sanitized_use(ptr2);
    validated_use(ptr2);
    incorrect_validated_use(ptr2);
    missing_edge(ptr2);
}