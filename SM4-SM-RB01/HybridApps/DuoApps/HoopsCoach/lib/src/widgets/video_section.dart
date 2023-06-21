import 'package:flutter/material.dart';
import 'package:flutter/services.dart';

import 'package:video_player/video_player.dart';

class VideoSection extends StatefulWidget {
  const VideoSection({Key? key, required this.title, required this.asset}) : super(key: key);
  final String title;
  final String asset;

  @override
  State<VideoSection> createState() => VideoSectionState();
}

class VideoSectionState extends State<VideoSection> {
  late Future<void> _initializeVideoPlayerFuture;
  late VideoPlayerController controller;

  @override
  void initState() {
    controller = VideoPlayerController.asset("assets/videos/${widget.asset}.mp4");
    _initializeVideoPlayerFuture = controller.initialize();
    controller.setVolume(0.0);
    controller.setLooping(true);
    super.initState();
  }

  @override
  void dispose() {
    controller.dispose();
    super.dispose();
  }

  @override
  Widget build(BuildContext context) {
    return Padding(
      padding: const EdgeInsets.symmetric(vertical: 8.0, horizontal: 8.0),
      child: SizedBox(
        width: MediaQuery.of(context).size.width,
        height: MediaQuery.of(context).size.height * .28,
        child: Column(
          crossAxisAlignment: CrossAxisAlignment.start,
          children: [
            Text(
              widget.title,
              textAlign: TextAlign.left,
              style: const TextStyle(
                color: Colors.white,
                fontSize: 25,
                fontWeight: FontWeight.bold
              ),
            ),
            const SizedBox(height: 10),
            SizedBox(
              height: MediaQuery.of(context).size.height * .235,
              width: double.infinity,
              child: FutureBuilder(
                future: _initializeVideoPlayerFuture,
                builder: (context, snapshot) {
                  if (snapshot.connectionState == ConnectionState.done) {
                    return Stack(
                      alignment: Alignment.bottomCenter,
                      children: [
                        AspectRatio(
                          aspectRatio: controller.value.aspectRatio,
                          child: VideoPlayer(controller),
                        ),
                        Row(
                          children: [
                            IconButton(
                              onPressed: () {
                                HapticFeedback.lightImpact();
                                if (controller.value.isPlaying){
                                  controller.pause();
                                } else {
                                  controller.play();
                                }
                                setState(() {});
                              },
                              icon: Icon(
                                controller.value.isPlaying ? Icons.pause : Icons.play_arrow,
                                color: Colors.white
                              )
                            ),
                            IconButton(
                              onPressed: () {
                                controller.seekTo(const Duration(seconds: 0));
                                setState(() {});
                              },
                              icon: const Icon(
                                Icons.stop,
                                color: Colors.white
                              )
                            )
                          ],
                        ),
                        VideoProgressIndicator(
                          controller,
                          allowScrubbing: true,
                          colors: const VideoProgressColors(
                            backgroundColor: Colors.grey,
                            playedColor: Colors.white,
                            bufferedColor: Colors.black
                          )
                        ),
                      ]
                    );
                  } else {
                    return const Center(child: CircularProgressIndicator());
                  }
                }
              ),
            ),
          ],
        ),
      ),
    );
  }
}
