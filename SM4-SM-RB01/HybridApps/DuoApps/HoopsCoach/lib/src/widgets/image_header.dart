import 'package:flutter/material.dart';

import 'package:custom_rating_bar/custom_rating_bar.dart';
import 'package:dropdown_button2/dropdown_button2.dart';
import 'package:flutter/services.dart';
import 'package:image_picker/image_picker.dart';
import 'package:go_router/go_router.dart';

import 'package:app/src/models/shooting_exercise.dart';
import 'package:app/src/models/analysis_item.dart';

class ImageHeader extends StatefulWidget {
  const ImageHeader({
    required this.exercise,
    required this.description,
    required this.asset,
    super.key
  });

  final ShootingExercise exercise;
  final String description;
  final String asset;

  @override
  State<StatefulWidget> createState() => ImageHeaderState();
}

class ImageHeaderState extends State<ImageHeader> {
  final ImagePicker _picker = ImagePicker();

  @override
  Widget build(BuildContext context) {
    return Stack(
      alignment: AlignmentDirectional.center,
      clipBehavior: Clip.hardEdge,
      children: [
        Container(
          alignment: Alignment.center,
          width: MediaQuery.of(context).size.width,
          decoration: BoxDecoration(
            gradient: LinearGradient(
              begin: Alignment.topCenter,
              end: Alignment.bottomCenter,
              colors: [
                Colors.black.withOpacity(.6),
                Colors.black
              ],
              stops: const [0.0, 1],
              tileMode: TileMode.clamp
            )
          ),
          child: Image.asset(
            "assets/${widget.asset}.png",
            width: MediaQuery.of(context).size.width,
            fit: BoxFit.cover
          ),
        ),
        Column(
          crossAxisAlignment: CrossAxisAlignment.start,
          children: [
            Text(
              widget.exercise.exerciseTitle,
              textAlign: TextAlign.left,
              style: const TextStyle(
                color: Colors.white,
                fontSize: 40,
                fontWeight: FontWeight.bold
              ),
            ),
            SizedBox(
              width: MediaQuery.of(context).size.width * .8,
              child: Text(
                widget.description,
                textAlign: TextAlign.left,
                style: const TextStyle(
                  color: Colors.white,
                  fontSize: 20
                ),
              ),
            ),
            const SizedBox(height: 120),
            SizedBox(
              width: MediaQuery.of(context).size.width * .95,
              child: Row(
                mainAxisAlignment: MainAxisAlignment.start,
                children: [
                  RatingBar.readOnly(
                    filledIcon: Icons.star,
                    emptyIcon: Icons.star_border,
                    halfFilledIcon: Icons.star_half,
                    initialRating: widget.exercise.rating.toDouble(),
                    maxRating: 3,
                    filledColor: Colors.white,
                    emptyColor: Colors.white,
                    halfFilledColor: Colors.white,
                    size: 35
                  ),
                  SizedBox(width: MediaQuery.of(context).size.width * .25),
                  DropdownButtonHideUnderline(
                    child: DropdownButton2(
                      onMenuStateChange: (_) => HapticFeedback.heavyImpact(),
                      customButton: Container(
                        width: MediaQuery.of(context).size.width * .3,
                        decoration: BoxDecoration(
                          borderRadius: BorderRadius.circular(16),
                          color: Colors.orange
                        ),
                        child: Padding(
                          padding: const EdgeInsets.symmetric(horizontal: 8.0, vertical: 10.0),
                          child: Row(
                            mainAxisAlignment: MainAxisAlignment.spaceEvenly,
                            children: const [
                              Icon(Icons.sports_basketball),
                              Text("Practice")
                            ],
                          ),
                        ),
                      ),
                      items: [
                        ...AnalysisItem.analysisKinds.map((item) => DropdownMenuItem<AnalysisItem>(
                            value: item,
                            child: AnalysisItem.buildItem(item),
                          ),
                        ),
                      ],
                      onChanged: (value) async {
                        String route = "";

                        HapticFeedback.heavyImpact();
                        if (value?.name == "Shoot Analysis") {
                          XFile? video = await _picker.pickVideo(source: ImageSource.gallery);

                          if (video == null || !mounted) {
                            return;
                          }

                          route = "/exercises/shooting/free_throws/analysis/shoot";
                        } else {
                          XFile? image = await _picker.pickImage(source: ImageSource.gallery);

                          if (image == null || !mounted) {
                            return;
                          }

                          route = "/exercises/shooting/free_throws/analysis/posture";
                        }
                        if (route != "" && mounted) {
                          GoRouter.of(context).go(route);
                        }
                      },
                      dropdownStyleData: DropdownStyleData(
                        width: 185,
                        padding: const EdgeInsets.symmetric(vertical: 6),
                        decoration: BoxDecoration(
                          borderRadius: BorderRadius.circular(4),
                          color: Colors.redAccent,
                        ),
                        elevation: 8,
                        offset: const Offset(0, 8),
                      ),
                      menuItemStyleData: MenuItemStyleData(
                        customHeights: [
                          ...List<double>.filled(AnalysisItem.analysisKinds.length, 48),
                        ],
                        padding: const EdgeInsets.only(left: 16, right: 16),
                      ),
                    )
                  )
                ],
              ),
            )
          ],
        ),
      ],
    );
  }
}
