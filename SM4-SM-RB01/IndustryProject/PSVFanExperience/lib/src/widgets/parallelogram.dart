import 'package:flutter/material.dart';

class Parallelogram extends CustomClipper<Path> {
  @override
  Path getClip(Size size) {
    final path = Path();
    const slant = 30.0;

    path.lineTo(0, 0);
    path.lineTo(size.width, 0);
    path.lineTo(size.width, size.height - slant);
    path.lineTo(0, size.width);
    path.close();
    return path;
  }

  @override
  bool shouldReclip(CustomClipper<Path> oldClipper) {
    return false;
  }
}