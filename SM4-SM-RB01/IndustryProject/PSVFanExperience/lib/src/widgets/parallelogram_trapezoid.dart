import 'package:flutter/material.dart';

class TrapezoidClipper extends CustomClipper<Path> {
  @override
  Path getClip(Size size) {
    final path = Path();
    const slant = 30.0;

    path.lineTo(slant, 0);
    path.lineTo(0, size.height);
    path.lineTo(size.width - slant, size.height);
    path.lineTo(size.width, 0);
    path.close();
    return path;
  }

  @override
  bool shouldReclip(CustomClipper<Path> oldClipper) {
    return false;
  }
}