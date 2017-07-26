//list.c
#include <stdlib.h>
#include <stdio.h>
#include "list.h"

struct list *new_list(int* value, struct list *next){
    struct list *this = malloc(sizeof(struct list));
    this->value = value;
    this->next = next;
    return this;
}


















