#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>

/* These functions are defined by compiling a well-formed CLO source 
 * program. */
extern int program(int argc, int* argv);
extern void clo_init();


/************************
 * CLO Internal Functions
 ************************/

int* clo_malloc(int size) {
  return (int*)malloc(size);
}

int* clo_alloc_array (int size) {
  assert (size >= 0);
  int *arr = (int*)malloc(sizeof(int) * (size+1));
  arr[0] = size;
  return arr;
}	

void clo_array_bounds_check(int bound, int index) {
  if ((0 <= index) && (index < bound)) return;
  fprintf(stderr, "Array bounds violation: bound = %d index = %d.\n", bound, index);
  exit(-1);
}


/************************
 * CLO Builtin Functions 
 ************************/
int* array_of_string (char *str) {
  int len, i, *arr;
  char *p;

  assert (NULL != str);

  len = strlen(str);
  assert (len >= 0);

  arr = (int*)malloc(sizeof(int) * (len+1));
  arr[0] = len;
  for (i=0; i<len; i++) {
    arr[i+1]=(int)str[i];
  }

  return arr; 
}


int* string_of_array (int *arr) {
  int len, i;
  char *str;

  assert (NULL != arr);

  len = arr[0];
  assert (len >= 0);

  str = malloc(sizeof(char) * (len+1));
  
  for (i=0; i<len; i++) {
    str[i] = (char)arr[i+1];
    assert (0 != str[i]);
  }
  str[len] = 0;

  return (int*)(str);
}

void print_string (int* str) {
  assert (NULL != str);
  printf ("%s", (char*)str);
}

void print_int (int i) {
  printf ("%d", i);
}

void print_bool (int i) {
  printf ("%d", i);
}


/* 
 * Convert the argv array into an CLO array of 
 * type string[]
 * Invoke the CLO 'program' entry point after
 * initializing the global variables.
 * Prints the results of the CLO program call 
 * to the terminal.
 */
int main(int argc, char* argv[]) {
  int *clo_argv, i, result;

  clo_argv = clo_alloc_array(argc); 

  /* Copy the string pointers to the correct places. */
  for (i=0; i<argc; i++){
    clo_argv[i+1] = (int)argv[i];
  }

  /* Call the initialization code. */
  clo_init();
  result = program(argc, clo_argv);
  printf("%d\n", result);
  return result;
}
