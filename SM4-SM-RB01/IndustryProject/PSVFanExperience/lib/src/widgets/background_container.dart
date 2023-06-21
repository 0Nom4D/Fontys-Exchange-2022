import 'package:flutter/material.dart';

class Background extends StatelessWidget {
  const Background({this.color = "white", required this.child, super.key});

  final String? color;
  final Widget child;

  @override
  Widget build(BuildContext context) {
    return Container(
      width: double.infinity,
      decoration: BoxDecoration(
        image: DecorationImage(
          image: color == "red"
            ? const AssetImage('assets/images/DrawerBG.png')
            : const AssetImage('assets/images/background-light.png'),
          fit: BoxFit.cover,
        ),
      ),
      child: child
    );
  }
}