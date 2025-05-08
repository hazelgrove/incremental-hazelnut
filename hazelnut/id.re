module Id = {
  type t = int;

  type counter = ref(int);

  let initial_counter = (): counter => ref(0);

  let fresh = (counter: counter): t => {
    let i = counter.contents;
    counter.contents = counter.contents + 1;
    i;
  };
};
