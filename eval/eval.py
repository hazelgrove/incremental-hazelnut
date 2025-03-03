import time
import subprocess
import json

COUNTER = 0
def count():
    global COUNTER
    ret = COUNTER
    COUNTER += 1
    return ret

path = time.strftime("%y-%m-%d-%H-%M-%S", time.localtime(time.time()))

def shell(str):
    print(str)
    subprocess.run(str, shell=True, check=True)

shell("mkdir -p log")
shell("rm log/* || true")
shell(f"dune exec eval {path}")

import dominate
from dominate.tags import *
import matplotlib.pyplot as plt
import numpy as np
import math

class make_doc(dominate.document):
    def _add_to_ctx(self): pass # don't add to contexts

def write_to(path, val):
    with open(path, "w") as f:
        f.write(val)

def readlines_file(path):
    with open(path, "r") as f:
        return f.readlines()

out_path = f"out/{path}/"
shell(f"rm -rf out/* || true")
shell(f"mkdir -p {out_path}")

doc = make_doc(title=out_path)

data = {}
for l in readlines_file(f"log/{path}"):
    j = json.loads(l)
    name = j["name"]
    iter = j["iter"]
    time = j["time"]
    if iter not in data:
        data[iter] = {}
    assert name not in data[iter]
    data[iter][name] = time

times = []
for m in data.values():
    times.append((m["incr"], m["baseline"]))

fig1, ax1 = plt.subplots(layout='constrained')

fig2, ax2 = plt.subplots(layout='constrained')

with doc:
    def scatterplot():
        xs = [times[i][0] for i in range(len(times))]
        ys = [times[i][1] for i in range(len(times))]
        min_value = min(min(*xs), min(*ys))
        max_value = max(max(*xs), max(*ys))
        ax1.scatter(xs, ys, color="#1f77b4", alpha=0.3, edgecolor="none")
        ax1.plot([min_value, max_value], [min_value, max_value], color="black")
        ax1.set_xscale('log')
        ax1.set_yscale('log')
        #ax1.set_xlim(min_value / 2, max_value * 2)
        #ax1.set_ylim(min_value / 2, max_value * 2)

    scatterplot()

    def cdf():
        cdf_x = sorted([times[i][1]/times[i][0] for i in range(len(times))])
        cdf_y = [(i + 1)/len(cdf_x) for i in range(len(cdf_x))]

        pct_slowdown = np.interp(1.0, cdf_x, cdf_y)
        ax2.plot(cdf_x, cdf_y)
        ax2.axvline(x=1,c='black',linewidth=0.5)
        ax2.annotate('{:.0f}%'.format(pct_slowdown * 100), xy=(1, pct_slowdown), xytext=(-50, 0), textcoords='offset points', bbox = dict(boxstyle="round", fc="0.8"), arrowprops = dict(arrowstyle="->"))
        x_range = math.exp(max(abs(math.log(max(cdf_x))), abs(math.log(min(cdf_x)))))
    
    cdf()
    pic_path = f"{count()}.png"
    fig1.savefig(out_path + pic_path)
    img(src=pic_path)

    pic_path = f"{count()}.png"
    fig2.savefig(out_path + pic_path)
    img(src=pic_path)

        
write_to(out_path + "index.html", str(doc))

# subprocess.run(f"xdg-open {out_path}/index.html", shell=True, check=True)