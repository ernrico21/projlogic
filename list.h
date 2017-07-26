//list.h
#ifndef LIST_H
#define LIST_H

struct list {
  int* value;
  struct list *next;
};


struct list *new_list(int* value, struct list *tail);

#endif
