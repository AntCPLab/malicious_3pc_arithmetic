#!/usr/bin/env python3

# test model output by torch_mnist_dense.mpc

import torchvision
import torch
import torch.nn as nn
import numpy

net = nn.Sequential(
    nn.Flatten(),
    nn.Linear(28 * 28, 128),
    nn.ReLU(),
    nn.Linear(128, 128),
    nn.ReLU(),
    nn.Linear(128, 10)
)

f = open('Player-Data/Binary-Output-P0-0')

state = net.state_dict()

for name in state:
    shape = state[name].shape
    size = numpy.prod(shape)
    var = numpy.fromfile(f, 'double', count=size)
    var = var.reshape(shape)
    state[name] = torch.Tensor(var)

net.load_state_dict(state)

transform = torchvision.transforms.Compose(
    [torchvision.transforms.ToTensor()])

with torch.no_grad():
    ds = torchvision.datasets.MNIST(root='/tmp', transform=transform,
                                    train=False)
    total = correct_classified = 0
    for data in torch.utils.data.DataLoader(ds, batch_size=128):
        inputs, labels = data
        outputs = net(inputs)
        _, predicted = torch.max(outputs.data, 1)
        total += labels.size(0)
        correct_classified += (predicted == labels).sum().item()
    test_acc = (100 * correct_classified / total)
    print('Test accuracy of the network: %.2f %%' % test_acc)
