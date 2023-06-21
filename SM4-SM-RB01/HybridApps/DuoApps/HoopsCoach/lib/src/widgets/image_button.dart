import 'package:flutter/material.dart';
import 'package:flutter/services.dart';
import 'package:go_router/go_router.dart';

class ImageButton extends StatelessWidget {
  const ImageButton({
    required this.text,
    required this.asset,
    required this.toNavigate,
    super.key
  });

  final String text;
  final String asset;
  final String toNavigate;

  @override
  Widget build(BuildContext context) {
    return GestureDetector(
      onTap: toNavigate != "" ? () => {
        GoRouter.of(context).go(toNavigate),
        HapticFeedback.heavyImpact()
      }: null,
      child: Ink(
        height: 125,
        decoration: BoxDecoration(
          color: Colors.black,
          borderRadius: const BorderRadius.all(Radius.circular(25.0)),
          image: DecorationImage(
            image: AssetImage("assets/$asset.png"),
            fit: BoxFit.cover
          )
        ),
        child: Row(
          mainAxisAlignment: MainAxisAlignment.end,
          children: [
            Text(
              text,
              textAlign: TextAlign.end,
              style: const TextStyle(
                fontWeight: FontWeight.bold,
                color: Colors.white,
                fontSize: 30
              )
            ),
            const Icon(Icons.chevron_right, color: Colors.white)
          ]
        )
      )
    );
  }
}
