import 'package:custom_rating_bar/custom_rating_bar.dart';
import 'package:flutter/material.dart';
import 'package:flutter/services.dart';
import 'package:go_router/go_router.dart';

class ExerciseButton extends StatelessWidget {
  const ExerciseButton({
    required this.text,
    required this.asset,
    required this.rating,
    required this.toNavigate,
    super.key
  });

  final String text;
  final String asset;
  final int rating;
  final String toNavigate;

  @override
  Widget build(BuildContext context) {
    return SizedBox(
      height: 180,
      child: Card(
        shape: RoundedRectangleBorder(
          borderRadius: BorderRadius.circular(10.0),
        ),
        elevation: 2.0,
        child: InkWell(
          onTap: toNavigate != "" ? () => {
            HapticFeedback.heavyImpact(),
            GoRouter.of(context).go(toNavigate)
          }: null,
          child: ListTile(
            title: Column(
              children: [
                Row(
                  mainAxisAlignment: MainAxisAlignment.spaceBetween,
                  children: [
                    Text(
                      text,
                      style: const TextStyle(
                        fontSize: 40,
                        fontWeight: FontWeight.bold
                      ),
                    ),
                    Transform.translate(
                      offset: const Offset(0, 21),
                      child: Image.asset(
                        "assets/$asset.png",
                        fit: BoxFit.cover
                      )
                    )
                  ],
                ),
                Transform.translate(
                  offset: const Offset(0, -20),
                  child: RatingBar.readOnly(
                    filledIcon: Icons.star,
                    emptyIcon: Icons.star_border,
                    halfFilledIcon: Icons.star_half,
                    initialRating: rating.toDouble(),
                    maxRating: 3,
                    filledColor: Colors.black,
                    emptyColor: Colors.black,
                    halfFilledColor: Colors.black,
                    size: 25
                  ),
                )
              ]
            ),
          )
        )
      ),
    );
  }
}
