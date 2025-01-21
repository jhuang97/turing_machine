# turing_machine

Code for simulating Turing machines, especially the 5-state 2-symbol Turing machine known as Skelet 1.

The behavior of Skelet 1 is complicated and involves four levels of abstraction.  Eventually, it enters into an infinite loop where each cycle occurs shifted over on the tape -- therefore, Skelet 1 is a [translated cycler](https://wiki.bbchallenge.org/wiki/Translated_cycler).  Shawn Ligocki has some blog posts describing Skelet 1 in [more](https://www.sligocki.com/2023/02/25/skelet-1-wip.html) [detail](https://www.sligocki.com/2023/03/13/skelet-1-infinite.html).

Here, I have implemented a series of simulators for increasingly accelerated simulations of Skelet 1:
1. The basic Turing machine simulation - operates on ones and zeros
2. Run length encoding simulation - run length enconding of the 1s
3. Counter simulation
4. Counter simulation with the stride rule
5. Counter simulation with the stride rule and uni-cycles

Previously, it was not known when exactly Skelet 1 enters into the infinite loop, as it is kind of tedious to figure out how many base steps it takes to complete one stride or one set of uni-cycles.  This is what I worked on: if my math is not wrong, then Skelet 1 enters into the infinite cycle at around 
$$5418883027667422764169643414989497193809945789706483 \approx 5.42 \times 10^51 \text{ base steps,}$$
give or take one or two cycle periods.

The main method is currently set to run an accelerated simulator all the way to the translated cycle.

The folder `turing_machine_traces/` contains some other simulation traces for Skelet 1.

While writing this code, I referred to @uni's [Skelet 1 simulator](https://github.com/univerz/bbc/tree/no1).